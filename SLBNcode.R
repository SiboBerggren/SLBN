##required packages;
library(bnlearn); library(Rgraphviz); library(expm)

#################################################################
## by Simon Berggren, jan 2015, updated april 2015
##
## input: data.frame, with data from a sufficient, stable distrubution.
## 
## Usage: SLBN(data:(data.frame), alpha:(real), info:(bool),
##               viewGraph:bool, sCheck:(bol)
##
## sCheck prevents the synchronization of the MBs.
## output: list object:
## [1] adjacency matrix for maximally oriented graph,
## [2] BIC score of the structure (0 i undirected), 
## [3] # tests performed.
##
## namingconventions, not very consistent, 
##
##

SLBN<-function(data, alpha=0.05, info=FALSE, viewGraph=TRUE, sCheck=TRUE){
  
  ## global variables, requierd by static functions
  obs<-length(data[,1]);
  var<-length(data);
  names<-names(data);
  MBdomain<-list();
  colliders<-c(); ##never used...
  Vedges<-c();    ##contains pairs of nodes, {1->2,1->3,...}
  edges<-matrix(rep(0,var^2),ncol=var);
  dirEdges<-matrix(rep(0,var^2),ncol=var);
  detEdges<-matrix(rep(0,var^2),ncol=var);
  rownames(dirEdges)<-names; colnames(dirEdges)<-names;
  directed <- FALSE;
  tests<-0;
  
  #returns subset na\{nb,b}
  sset<-function(na,nb,b){
    na<-na[which(na!=b)];
    for(v in nb){
      na<-na[which(na!=v)];
    }
    return(na);
  }
  
  #returns neighbors of i
  nbh<-function(i){ 
    nb<-c();
    for(j in 1:var){
      if(edges[i,j]==1){
        nb<-c(nb,j);
      }
    }
    return(nb);
  }
    
  ## returns powerset of set C
  pSet<-function(C){
    if(length(C)==0) return(numeric());
    pset=vector(mode="list",length=(length(C)^2-1));
    pset[[1]] = numeric(); 
    for(i in 1:length(C)){
      f<-2^(i-1); 
      for(subset in 1:f){ 
        pset[[f+subset]] = c(pset[[subset]],C[i]);
      }
    }
    return(pset)
  }
  
  ## test ind. X ind Y| set Z, returns p-value
  independent<-function(X,Y,Z=c()){
    if(length(Z)==0){p<-ci.test(data[X][,],data[Y][,])$p.value;}
    else{p<-ci.test(data[X][,],data[Y][,],data[Z][,])$p.value;}
    return(p);
  }
  
  ## used in step 1, returns var not in S and !=i
  examine<-function(S=c(), i){
    ex<-c();
    for(k in seq(1,var)){ 
      if(k!=i&!(k%in%S)) {ex<-c(ex,k);} 
    }
    return(ex);
  }
  
  ## boolean, is there a directed path from a->b?
  path<-function(a,b){
    for(i in 1:var){
      if((detEdges%^%i)[a,b]>0){
        return(TRUE);
        break;
      }
    }
    return(FALSE);
  }
  
  ## boolean, graph contains cycles?
  cycle<-function(){
    bol<-FALSE;
    for(i in 1:var){
      if(path(i,i)){
        bol<-TRUE;
      }
    }
    return(bol);
  }
  
  ## boolean, set contains edge?
  containsEdge<-function(a,b,set){
    if(length(set)<1) return(FALSE);
    for(i in seq(from=1,to=(length(set)-1),by=2)){
      if(set[i]==a&set[i+1]==b){
        return(TRUE);
      }
    }
    return(FALSE);
  }
  
  ## return most common edge in set, requires a set accepted by containsEdge
  commonEdge<-function(set){
    common<-c();
    count<-c();
    for(i in seq(1,(length(set)-1),by=2)){
      if(containsEdge(set[i],set[i+1],common)){
        count[i]<-count[i]+1;
      }
      else{
        count[i]<-1;
      }
    }
    maxIndex<-0;
    maxCount<-0;
    for(i in seq(1,length(set)-1,by=2)){
      if(count[i]>maxCount){
        maxCount<-count[i];
        maxIndex<-i;
      }
    }
    return(c(set[maxIndex],set[maxIndex+1]))
  }
  
  ## remove edge from set
  removeEdge<-function(a,b,set){
    newset<-c();
    for(i in seq(1,length(set)-1,by=2)){
      if(!(set[i]==a&set[i+1]==b)){
        newset<-c(newset,c(set[i],set[i+1]));
      }
    }
    return(newset);
  }
  
  ## remove Node from set, returns the new set.
  removeNode<-function(node,set){
    set<-set[-node];
    return(set);
  }
 
  
  ## for info
  prStart<-function(i){cat("\nObtaining Markov blanket of ",names[i],", growing:",sep="")}
  prGrowTest<-function(i,k,S=c(),p){cat("\n(",names[i],"ind",names[k],"|",toString(names[S]),
                                        "), p=",round(p,3),", ")}
  prGrowDep<-function(S=c()){cat("indicates dep. S={",toString(names[S]),"}, restarting",sep="")}
  prGrowInd<-function(){cat("indicates ind. S unchanged")}
  prShrink<-function(){cat(", shrinking:")}
  prShrinkTest<-function(i,k,S=c(),p){cat("\n(",names[i],"ind",names[k],"|",toString(names[S]),
                                          "), p=",round(p,3),", ")}
  prShrinkInd<-function(S=c()){cat("indicates ind. S={",toString(names[S]),"}, restarting")}
  prShrinkDep<-function(){cat("indicates dep. S unchanged.")}
  prRule3<-function(a,b){cat("\nRule 3 satisfied, orient",names[a],"->",names[b])}
  prVStart<-function(a){cat("\nCenternode:",names[a],",")}
  prVDet<-function(b,a,c){
    if(!containsEdge(a,b,Vedges)){
      cat("\tdetected V-structure: ",names[a],"->",names[b],"<-",names[c],sep="")
    }
  }
  prSkel<-function(i){cat("\nObtaining neighborhood of",names[i]);}
  prSkelSel<-function(k,U=c()){cat("\ntesting",names[k],", condition-set: {",toString(names[U]),
                                   "}, ");}
  prSkelInd<-function(i,k,U=c()){cat("(",names[i],"ind",names[k],"|",toString(names[U]),
                                     "), not neighbors");}
  prSkelDep<-function(i,k){cat("no separating set,",names[i],names[k],"neighbors")}
  prRule1<-function(c,b){cat("\nRule 1 satisfied, orient",names[c],"->",names[b])}
  prRule2<-function(i,count){cat("\nRule 2 satisfied, orient",names[i],"->",names[count])}
  prStep5comp<-function(S5){
    cat("\nStep 5 complete, detected orientations:");
    if(length(S5)>0){
      for(i in seq(1,length(S5)-1,by=2)){
        cat("\n",names[S5[i]],"->",names[S5[i+1]]);
      }
    }
  }
  
  
  ## the SLBN algorithm.  
  ## step 1
  if(info) cat("\nSLBN.\n");
  if(info) cat("\nStep 1, learn Markov blankets.\n")
  for(i in seq(1,var)){               ## growing-phase
    if(info) prStart(i);   
    S<-c();
    continue <- TRUE; changed <- FALSE;
    while(continue|changed){
      changed <- FALSE;
      for(k in examine(S,i)){         ##for variables not i and not in S
        p<-independent(i,k,S);        ##testing ind, cond. on S
        tests<-tests+1;
        if(info) prGrowTest(i,k,S,p); ##if not independent, include k in S 
        if(p<alpha){ 
          S<-c(S,k);
          changed<-TRUE; 
          if(info) prGrowDep(S)
          break;
        } 
        else{ 
          if(info) prGrowInd(); 
          changed<-FALSE
        }                             ##else ind. k not included in S
      }
      continue<-FALSE;
    }                                 ##shrinking-phase
    if(info){prShrink()}
    continue<-TRUE;
    while(continue|changed){
      changed<-FALSE;
      for(k in S){                    ##for each k in the blanket.
        p<-independent(i,k,s<-S[which(S!=k)]) ##testing ind. cond on S\k
        tests<-tests+1;
        if(info) prShrinkTest(i,k,s,p);
        if(p>alpha){
          S<-S[which(S!=k)];          ##if independent, exclude k
          if(info) prShrinkInd(S); 
          changed<-TRUE; 
          break;
        }
        else{                         ##else dependent. S unchanged
          if(info) prShrinkDep();
          changed<-FALSE;
        } 
        if(length(S)==0) break;
      }
      continue<-FALSE;
    }
    MBdomain[i]<-list(S);
  }
  
  #Symmetry check
  if(sCheck){
    for(nodeOne in 1:var){
      for(nodeTwo in MBdomain[[nodeOne]]){
        if(!nodeOne%in%MBdomain[[nodeTwo]]){
          unchanged<-TRUE;
          if(info){
            cat("\n",names[nodeTwo]," in MB(",names[nodeOne],"), but ",names[nodeOne],
                " not in MB(",names[nodeTwo],")",sep="");
          }
          C<-MBdomain[[nodeOne]][-nodeTwo]
          p<-independent(nodeOne,nodeTwo,C);
          tests<-tests+1;
          if(p>alpha*1.2){
            MBdomain[[nodeOne]]<-removeNode(MBdomain[[nodeOne]],nodeTwo);
            if(info){
              cat("\n",names[nodeTwo]," removed from MB(",names[nodeOne],")",sep="");
            }
            unchanged<-FALSE;
          }
          else{
            p<-independent(nodeOne,nodeTwo,MBdomain[[nodeTwo]]);
            tests<-tests+1;
            if(p<alpha*0.8){
              MBdomain[[nodeTwo]]<-c(MBdomain[[nodeTwo]],nodeOne);
              if(info){
                cat("\n",names[nodeOne]," included in MB(",names[nodeTwo],")",sep="");
              }
              unchanged<-FALSE;
            }
          }
          if(unchanged){
            if(info) cat("\nUnchanged, ambiguous test results...");
            warning("Assymetric MB's");
          }
        }
      }
    }
  }
  
  if(info) {cat("\nStep 1 complete, Markov blankets:");
    for(i in 1:var){
      cat("\n",names[i],":",toString(names[MBdomain[[i]]]))
    }
  }
  
  ##step 2
  if(info) cat("\n\nStep 2, learn neigborhoods, obtain skeleton.\n");
  tested<-c();
  for(i in seq(1,var)){
    if(info) prSkel(i);
    for(k in (mbi<-MBdomain[[i]])){
      mbk<-MBdomain[[k]];
      if(length(mbi[which(mbi!=k)])<=length(mbk[which(mbk!=i)])){
        U<-mbi[which(mbi!=k)]
      }
      else{
        U<-mbk[which(mbk!=i)];
      }
      if(info) prSkelSel(k,U);
      indep<-FALSE;
      for(j in pSet(U)){
        tests<-tests+1;
        if(independent(i,k,j)>alpha){
          if(info) prSkelInd(i,k,j);
          tested<-c(c(k,i),tested);
          indep<-TRUE;
          break;
        }
      }
      if(!indep){
        if(info) prSkelDep(i,k);
        if(containsEdge(i,k,tested)){
          warning("\nambiguity when connecting ",names[i]," and ",names[k]);
        }
        edges[i,k]=edges[k,i]<-1;
        dirEdges[i,k]=dirEdges[k,i]<-1;
      }
    }
  }
  if(info){ cat("\nStep 2 complete, neighbors:")
    for(i in 1:var){
      cat("\n",names[i],":",names[nbh(i)]);
    }
  }
  
  ## step 3
  if(info) cat("\n\nStep 3, propagate V-structures.\n");
  for(a in seq(1,var)){
    if(info) prVStart(a);
    for(b in (na<-nbh(a))){
      tested<-FALSE;
      indep=FALSE;
      nb<-nbh(b);
      for(c in sset(na,nb,b)){
        mbb<-MBdomain[[b]];
        mbc<-MBdomain[[c]];
        if(length(U1<-mbb[which(mbb!=a&mbb!=c)])<=length(U2<-mbc[which(mbc!=a&mbc!=b)])){
            U<-U1;
          }
        else{
            U<-U2;
          }
        if(length(U)==0){#&!tested){
          tests<-tests+1;
          if(independent(b,c,a)>alpha){
            tested<-TRUE; indep<-TRUE; 
            break;
          }
          tested<-TRUE;
        }
        else{
          for(s in pSet(U)){
            tests<-tests+1;
            if(independent(b,c,c(a,s))>alpha){
              indep=TRUE; tested<-TRUE;
              break;  
            }
            tested<-TRUE;
          }
        }
        if(!indep&tested){
          dirEdges[a,b]<-0;
          detEdges[b,a]<-1;
          dirEdges[a,c]<-0;
          detEdges[c,a]<-1;
          directed <- TRUE;
          if(info) prVDet(a,b,c);
          Vedges<-c(Vedges,c(b,a));
          Vedges<-c(Vedges,c(c,a));
          break;
        }
      }
    }
  }
  
  if(info){
    cat("\nStep 3 complete, detected orientations:")
    for(i in 1:var){
      for(j in 1:var){
        if(dirEdges[i,j]>dirEdges[j,i]){
          cat("\n",names[i],"->",names[j]);
          colliders<-c(colliders,j)
        }
      }
    }
  }
  
  ## Step 4
  if(cycle()){
    if(info) cat("\n\nStep 4, Graph contains cycles");
    C<-c();
    R<-c();
    for(a in 1:var){
      for(b in nbh(a)){
        if(containsEdge(a,b,Vedges)&path(a,a)){
          C<-c(C,c(a,b));
        }
      }
    }
    while(cycle()){
      edge<-commonEdge(C);
      C<-removeEdge(edge[1],edge[2],C);
      detEdges[edge[1],edge[2]]<-0;
      R<-c(edge,R);
    }
    for(i in seq(1,length(R)-1,by=2)){
      a<-R[i];
      b<-R[i+1];
      dirEdges[a,b]<-0;
      dirEdges[b,a]<-1;
      detEdges[a,b]<-0;
      detEdges[b,a]<-1;
      removeEdge(a,b,Vedges);
      Vedges<-c(Vedges,c(b,a));
      if(info) cat("\nEdge (",a,",",b,") reversed");
    }
    if(info) cat("\n\nStep 4 complete, graph acyclic.");
  }
  else if(info){
    cat("\n\nStep 4, Graph is acyclic");
  }
  
  ##step 5
  if(info){cat("\n\nStep 5, orient compelled edges")}
  S5<-c();
  continue<-TRUE;
  while(continue){
      
    changed<-FALSE;
    ## rule 1
    for(c in 1:var){
      if(length(n<-nbh(c))>1){  #there are at least two neighbors
        for(a in n){
          for(b in n[which(n!=a)]){
            if(!a%in%nbh(b)&dirEdges[c,a]==0&dirEdges[b,c]==1&dirEdges[c,b]==1){
              detEdges[c,b]<-1;
              if(cycle()){
                detEdges[c,b]<-0;
                break;
              }
              dirEdges[b,c]<-0;
              detEdges[c,b]<-1;
              S5<-c(S5,c,b);
              changed<-TRUE;
              if(info) prRule1(c,b);
              break;
            }
          }
          if(changed) break;
        }
      }
      if(changed) break;
    }
    ## rule 2
    if(!changed){
      for(i in 1:var){
        if(length(nbh(i))>1){
          for(j in length(nbh(i))){
            if(dirEdges[j,i]==1&dirEdges[i,j]==1&path(i,j)){
              if(info) prRule2(i,j);
              dirEdges[j,i]<-0;
              detEdges[i,j]<-1;
              S5<-c(S5,i,j);
              changed<-TRUE;
              break;
            }
          }
          if(changed) break;
        }
      }
    }
    ## rule 3
    if(!changed){
      for(a in a:var){
        if(length(nbh(a))>2){
          for(b in nbh(a)){
            if(b%in%nbh(b)&length(nbh(b))>2){
              for(c in nbh(a)[which(nbh(a)!=b)]){
                if(c%in%nbh(a)&c%in%nbh(b)&dirEdges[c,a]==1&detEdges[c,b]==1){
                  for(d in nbh(a)[which(nbh(a)!=c&nbh(a)!=b)]){
                    if(!(d%in%nbh(c))&dirEdges[d,a]==1&detEdges[d,b]==1){
                      if(info){prRule3(a,b)}
                      dirEdges[b,a]<-0;
                      detEdges[a,b]<-1;
                      S5<-c(S5,a,b);
                      changed<-TRUE;
                      break;
                    }
                  }
                }
                if(changed) break;
              }
            }
            if(changed) break;
          }
        }
        if(changed) break;
      }
    }
    if(!changed){
      continue<-FALSE;
    }
  }
  
  if(info) prStep5comp(S5);
  
  ## SLBN complete ##
    
  
  ## construct and plot graphviz-object
  graph<-empty.graph(names);
  amat(graph, ignore.cycles=TRUE)<-dirEdges;
  if(viewGraph) {graphviz.plot(graph)};
  
  ## compute BIC-score, if defined
  score = tryCatch({
    score(cextend(graph), data, type="bic")
  }, warning = function() {
    return(NA);
  }, error = function(e) {
    return(NA)
  }, finally = {}
  )
  
      
  if(info){
    cat("\n\nSLBN complete, Adjacency Matrix:\n\n");
    print(dirEdges);
    cat("\nBIC: ",score, ", number of tests: ",tests,sep="");
  }
  
  return(list(dirEdges, score, tests));
}