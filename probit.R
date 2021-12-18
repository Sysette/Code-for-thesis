probit <- function(fixed,random,subject.name="id",item.name="item",response.name=NULL,Gamma=NULL,data,BB=10,maxit=50) {
  # item and response name
  if ((!is.character(item.name))|(length(item.name)==0)) stop("item.name must be a non-vanishing character")
  if (is.null(response.name)) response.name <- paste(item.name,"value",sep=".")
  if ((!is.character(response.name))|(length(response.name)==0)) stop("response.name must be a non-vanishing character or NULL")
  
  # find items and make sanity check
  items <- all.vars(fixed[[2]])
  if (!all(sapply(wide.data[,items],function(x){is.factor(x)}))) stop("Response variables must be factor")
  items.ordinal <- items[sapply(wide.data[,items],is.factor)]
  
  # take levels of factors and recode them as numeric
  ordinal.levels <- as.list(rep(NA,length(items.ordinal)))
  names(ordinal.levels) <- items.ordinal
  for (i in c(items.ordinal)) {
    ordinal.levels[[i]] <- levels(wide.data[[i]])
    wide.data[[i]] <- as.numeric(wide.data[[i]])
  }
  
  # check random effects
  d <- length(random)
  if (d < 2) stop("Present implementation assumes at least two random effects")
  
  # find subjects
  subjects <- unique(wide.data[[subject.name]])
  
  # if item.name appears in data then it is removed
  if (is.element(item.name,names(data))) {
    warning("Variable ",item.name," is removed from data as it is used as item.name")
    data <- select(data,-any_of(item.name))
  }
  
  # if response.name appears in data then it is removed
  if (is.element(response.name,names(data))) {
    warning("Variable ",response.name," is removed from data as it is used as response.name")
    data <- select(data,-any_of(response.name))
  }
  
  # Cholesky factor for variance of random effects
  if (is.null(Gamma)) {
    # if not prespecified, then initialize as the identity matrix
    Gamma <- diag(nrow=d)
  } else {
    # check format of Gamma
    if (nrow(Gamma)!=ncol(Gamma)) stop("Gamma must be NULL or a square matrix")
    if (nrow(Gamma)!=d) stop("Gamma must have number of columns equal to the number of random effects")
    if (det(Gamma)==0) stop("Gamma must be non-singular") 
  }
  
  # return result from Minimization-Maximization iterations
  return(MM_probit(maxit,
                   fixed,response.name,
                   item.name,items.ordinal,ordinal.levels,
                   subject.name,random,
                   eta=NULL,beta=NULL,Gamma=Gamma,
                   BB,
                   data))
  
}

log_pnorm <- function(a,b) {
  mysign <- -sign(pmin(a,b))
  log.b  <- pnorm(pmax(mysign*a,mysign*b),log.p=TRUE)
  log.a  <- pnorm(pmin(mysign*a,mysign*b),log.p=TRUE)
  log.b + ifelse(log.b-log.a<0.693,log(-expm1(log.a-log.b)),log1p(-exp(log.a-log.b)))
}

log_dnorm <- function(a,b){
  log.b  <- dnorm(pmax(a,b),log=TRUE)
  log.a  <- dnorm(pmin(a,b),log=TRUE)
  log.max <- pmax(log.b,log.a)
  log.min <- pmin(log.b,log.a)
  log.b + ifelse(log.max-log.min<0.693,
                 log(-expm1(log.min-log.max)),log1p(-exp(log.min-log.max)))
}

# Maximization-Maximization for probit model
MM_probit <- function(maxit,
                      fixed,response.name,
                      item.name,items.ordinal,ordinal.levels,
                      subject.name,random,
                      eta=NULL,beta=NULL,Gamma=Gamma,
                      BB,
                      data){
  
  # grab parameters
  d <- length(random)
  subjects <- unique(wide.data[[subject.name]])
  items <- c(items.ordinal)
  
  long.data <- pivot_longer(wide.data,items,names_to=item.name,values_to=response.name)
    
  # if NULL, then initialize eta else check if all levels is used
  fun <- function(i){
    tmp <- clm(factor(item.value)~1,data=subset(long.data,item==i))$alpha
    names(tmp) <- NULL
    return(tmp)}
  
  if (is.null(eta)) {
    eta <- vector("list",length(items))
    eta <- lapply(items, fun)
    names(eta) <- items
    for (i in c(items.ordinal)) {
      eta[[i]] <- append(eta[[i]],-Inf,after=0)
      eta[[i]] <- append(eta[[i]],Inf,after=length(eta[[i]]))
      }
  } else {
    for (i in c(unique(items))){
      if(length(eta[[i]])!=length(unique(wide.data[[i]]))+1){
        warning("Levels in ", names(eta[i]), " is removed")
        tmp <- setdiff(c(1:(length(eta[[i]])-1)),c(unique(wide.data[[i]])))
        eta[[i]] <- eta[[i]][-tmp]
        
        for (m in c(tmp)){
          wide.data[[i]][wide.data[[i]]>=m]<- wide.data[[i]][wide.data[[i]]>=m]-1}
      }}}
  
  
  
  Q <- matrix(0,d*d,d*(d+1)/2)
  Q[matrix(1:(d*d),d,d)[upper.tri(matrix(0,d,d),diag=TRUE)],] <- diag(nrow=d*(d+1)/2)
  tildeQ <- matrix(aperm(array(Q,dim=c(d,d,d*(d+1)/2)),c(1,3,2)),d*d*(d+1)/2,d)
  
  #model matrices 
  Z <- no.intercept(model.matrix(random,data=long.data))
  X <- model.matrix(delete.response(terms(fixed)),long.data) 
  
  csum=0
  from <- c()
  to <- c()
  for (i in 1:length(subjects)){
    from[i] <- 1+csum
    to[i] <- csum+sum(long.data$id==i)
    csum <- sum(long.data$id==i)+csum
  }
  
  csum1=0
  from1 <- c()
  to1 <- c()
  for (i in 1:length(subjects)){
    from1[i] <- 1+csum1
    to1[i] <- csum1+BB*sum(wide.data$id==i)
    csum1 <- BB*sum(wide.data$id==i)+csum1
  }
  
  csum2=0
  from2 <- c()
  to2 <- c()
  for (i in 1:length(subjects)){
    from2[i] <- 1+csum2
    to2[i] <- csum2+(d*(d+1)/2)
    csum2 <- (d*(d+1)/2)+csum2
  }
  
  # individual model matrices for the subjects
  liste1 <- vector(mode="list", length=length(subjects))
  for (i in 1:length(subjects)){
    X_s <- X[from[i]:to[i],]
    liste1[[i]] <- append(liste1[[i]],X_s)}
  
  Xs <- matrix(liste1, length(subjects))
  
  liste2 <- vector(mode="list", length=length(subjects))
  for (i in 1:length(subjects)){
    Z_s <- Z[from[i]:to[i],]
    liste2[[i]] <- append(liste2[[i]],Z_s)}
  
  Zs <- matrix(liste2, length(subjects))
  
  # simulate alpha_s^b BB times
  alpha <- matrix(NA,BB*length(wide.data[[subject.name]]),d)
  for (bb in 1:(BB*length(wide.data[[subject.name]]))){
    alpha[bb,] <- rnorm(d)
  }
  
  liste3 <- vector(mode="list", length=length(subjects))
  for (i in 1:length(subjects)){
    alpha_sb <- alpha[from1[i]:to1[i],]
    liste3[[i]] <- append(liste3[[i]],alpha_sb)}
  
  alphasb <- matrix(liste3, length(subjects))
  
  
  Gs <- function(x,d=length(random),B=BB) {
    # extract parameters
    mu <- x[1:d]
    psi <- x[-(1:d)]
    Psi <- matrix(Q%*%psi,d,d)
    invPsi <- solve(Psi)
    
    # compute sum(log(Phi(b)-Phi(a)))
    logpnorm <- 0
    for (bb in 1:B){
      a <- c()
      b <- c()
      for (i in 1:length(long.data$item.value[long.data[[subject.name]]==s])){
        a[i] <- c(mapply(function(x,y){x[y+1]},eta[long.data$item[long.data[[subject.name]]==s]],long.data$item.value[long.data[[subject.name]]==s])[i]-
                    (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta)[i]-
                    (matrix(Zs[[s,1]],sum(long.data[[subject.name]]==s),ncol(Z))%*%(mu+invPsi%*%matrix(alphasb[[s,1]],BB*sum(wide.data$id==s),d)[bb,]))[i])
        
        b[i] <- c(mapply(function(x,y){x[y]},eta[long.data$item[long.data[[subject.name]]==s]],long.data$item.value[long.data[[subject.name]]==s])[i]-
                    (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta)[i]-
                    (matrix(Zs[[s,1]],sum(long.data[[subject.name]]==s),ncol(Z))%*%(mu+invPsi%*%matrix(alphasb[[s,1]],BB*sum(wide.data[[subject.name]]==s),d)[bb,]))[i])}
      
      logpnorm <- logpnorm + log_pnorm(a,b)}
    
    # compute Gs
    log(det(Gamma)) - sum(log(abs(diag(matrix(Q%*%psi,d,d))))) - d/2  - sum(c(Gamma%*%invPsi)^2)/2 -
      sum(c(Gamma%*%mu)^2)/2 + (1/B)*(sum(logpnorm))
    
  }
  
  # compute gradient
  D_Gs <- function(x,d=length(random),B=BB) {
    # extract parameters
    r <- d*(d+1)/2   # psi dimension
    mu <- x[1:d]
    psi <- x[-(1:d)]
    Psi <- matrix(Q%*%psi,d,d)
    invPsi <- solve(Psi)
    invPsi.Q <- invPsi%*%matrix(tildeQ,d,r*d)
    
    x[d+cumsum(1:d)] <- x[d+cumsum(1:d)] + (x[d+cumsum(1:d)]==0)*1e-8
    one.psi <- rep(0,d*(d+1)/2); one.psi[cumsum(1:d)] <- 1/x[d+cumsum(1:d)]
    
    Gamma.invPsi.Q.invPsi <-
      matrix(aperm(array(matrix(Gamma%*%invPsi.Q,d*r,d)%*%invPsi,dim=c(d,r,d)),c(1,3,2)),d*d,r)
    
    l <- function(i){
      vec <- rep(0,r)      
      vec[i] <- 1
      return(vec)}
    
    Q.l <- vector(mode="list", length=r )
    for (i in 1:r){
      Q.l[[i]] <- append(Q.l[[i]],matrix(Q%*%l(i),d,d))}
    
    # compute the innersums for the gradient wrt mu and psi
    logdnormpnorm <- 0
    expinner <- matrix(NA,r,10)
    for (bb in 1:B){
      z <- vector(mode="list", length=r )
      a <- c()
      b <- c()
      for (m in 1:r){
        for (i in 1:length(long.data$item.value[long.data[[subject.name]]==s])){
          a[i] <- c(mapply(function(x,y){x[y+1]},eta[long.data$item[long.data[[subject.name]]==s]],long.data$item.value[long.data[[subject.name]]==s])[i]-
                      (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta)[i]-
                      (matrix(Zs[[s,1]],sum(long.data[[subject.name]]==s),ncol(Z))%*%(mu+invPsi%*%matrix(alphasb[[s,1]],BB*sum(wide.data$id==s),d)[bb,]))[i])
          
          b[i] <- c(mapply(function(x,y){x[y]},eta[long.data$item[long.data[[subject.name]]==s]],long.data$item.value[long.data[[subject.name]]==s])[i]-
                      (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta)[i]-
                      (matrix(Zs[[s,1]],sum(long.data[[subject.name]]==s),ncol(Z))%*%(mu+invPsi%*%matrix(alphasb[[s,1]],BB*sum(wide.data[[subject.name]]==s),d)[bb,]))[i])
          
          z[[m]][i] <-(matrix(Zs[[s,1]],sum(long.data[[subject.name]]==s),ncol(Z))%*%(invPsi%*%matrix(Q.l[[m]],d,d)%*%invPsi)%*%(matrix(alphasb[[s,1]],BB*sum(wide.data[[subject.name]]==s),d)[bb,]))[i]
        }
        inner_sum <- log_dnorm(a,b) - log_pnorm(a,b)
        expinner[m,bb]<-c(z[[m]])%*%exp(c(inner_sum))
      }
      
      logdnormpnorm <- logdnormpnorm + t(matrix(Zs[[s,1]],sum(long.data[[subject.name]]==s),ncol(Z)))%*%exp(inner_sum)
    }
    
    # compute the gradient wrt mu and psi
    c((-c(t(Gamma)%*%Gamma%*%mu) - (1/B)*(logdnormpnorm)),
      c(-one.psi + t(Gamma.invPsi.Q.invPsi)%*%c(Gamma%*%invPsi) + (1/B)*(c(rowSums(expinner)))))
  } 
  
  
  ELBO <- function(mu,psi,beta,eta,Gamma,B=BB) {
    Psi <- matrix(Q%*%psi,d,d)
    invPsi <- solve(Psi)
    
    logpnorm <- 0
    for (bb in 1:B){
      a <- c()
      b <- c()
      for (i in 1:length(long.data$item.value[long.data[[subject.name]]==s])){
        a[i] <- c(mapply(function(x,y){x[y+1]},eta[long.data$item[long.data[[subject.name]]==s]],long.data$item.value[long.data[[subject.name]]==s])[i]-
                    (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta)[i]-
                    (matrix(Zs[[s,1]],sum(long.data[[subject.name]]==s),ncol(Z))%*%(mu+invPsi%*%matrix(alphasb[[s,1]],BB*sum(wide.data$id==s),d)[bb,]))[i])
        
        b[i] <- c(mapply(function(x,y){x[y]},eta[long.data$item[long.data[[subject.name]]==s]],long.data$item.value[long.data[[subject.name]]==s])[i]-
                    (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta)[i]-
                    (matrix(Zs[[s,1]],sum(long.data[[subject.name]]==s),ncol(Z))%*%(mu+invPsi%*%matrix(alphasb[[s,1]],BB*sum(wide.data[[subject.name]]==s),d)[bb,]))[i])}
      
      logpnorm <- logpnorm + log_pnorm(a,b)}
    
    log(det(Gamma)) - sum(log(abs(diag(matrix(Q%*%psi,d,d))))) - d/2  - sum(c(Gamma%*%invPsi)^2)/2 -
      sum(c(Gamma%*%mu)^2)/2 + (1/B)*(sum(logpnorm))}
  
  # if NULL, then initialize beta, else check that beta has the right dim 
  if (is.null(beta)){
    beta0 <- c(1,2,3)
    v0 <- rep(0,d*(d+1)/2); v0[cumsum(1:d)]<-1
    x0 <- matrix(NA,length(subjects),d+d*(d+1)/2)  
                 
    for (i in 1:length(subjects)){
      x0[i,] <- c(rnorm(d),v0)}
    
    y0 <- matrix(NA,BB,length(long.data[[subject.name]]))
    za_e0 <- matrix(NA,BB,length(long.data[[subject.name]]))
    za0<- matrix(NA,BB,length(long.data[[subject.name]]))
    
    for(s in 1:length(subjects)){
      mu0 <- x0[s,1:d]
      psi0 <- x0[s,-(1:d)]
      Psi0 <- matrix(Q%*%psi0,d,d)
      
      alphas0 <- matrix(NA,d,BB*length(long.data$item[long.data[[subject.name]]==s]))
      for (i in 1:(BB*sum(long.data[[subject.name]]==s))){
        alphas0[,i] <- mu0 + solve(Psi0, rnorm(d))}
      
      zas0 <- matrix(NA,BB,sum(long.data[[subject.name]]==s))
      for (i in 1:sum(long.data[[subject.name]]==s)){
        zas0[,i] <- (matrix(Zs[[s,1]],sum(long.data[[subject.name]]==s),ncol(Z)))[i,]%*%alphas0[,(i*BB-(BB-1)):(i*BB)]}
      
      es0 <- matrix(NA,BB,sum(long.data[[subject.name]]==s))
      for (i in 1:sum(long.data[[subject.name]]==s)){
        es0[,i] <- rtruncnorm(1, a = mapply(function(x,y){x[y]},eta[long.data$item[long.data[[subject.name]]==s]],long.data$item.value[long.data[[subject.name]]==s])[i]-
                                (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta0)[i]- zas0[,i], 
                             
                             b = mapply(function(x,y){x[y+1]},eta[long.data$item[long.data[[subject.name]]==s]],long.data$item.value[long.data[[subject.name]]==s])[i]-
                               (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta0)[i]-zas0[,i])}
    
      za_e_s0=zas0+es0
      
      ys0 <- matrix(NA,BB,sum(long.data[[subject.name]]==s))
      for (i in 1:sum(long.data[[subject.name]]==s)){
        ys0[,i] <- (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta0)[i]+za_e_s0[,i]}
      
      za0[,from[s]:to[s]] <- zas0
      y0[,(from[s]:to[s])] <- ys0
      za_e0[,from[s]:to[s]] <- za_e_s0}
    
    vlong.data <- full_join(long.data,tibble(rep=1:BB), by=character()) %>% 
      add_column(za_e0=c(za_e0), y0=c(y0),za0=c(za0))
    
    m0 <- lm(update(fixed,y0~.+offset(za0)),data=vlong.data)
    vlong.data$all_effects <- predict(m0)
    beta <- as.numeric(coef(m0))}
    else{if (beta!=length(delete.response(terms(fixed)))+1) stop("beta must be a vector with length equal the colums of X")}
  
  #init optim values 
  v <- rep(0,d*(d+1)/2); v[cumsum(1:d)]<-1
  x1 <- matrix(NA,length(subjects),d+d*(d+1)/2)   
  for (i in 1:length(subjects)){
    x1[i,] <- c(rnorm(d,2,1),v)}
  
  conv <- c()
  elbo <- c()
  
  par <- matrix(NA,length(subjects),d+d*(d+1)/2)
  y <- matrix(NA,BB,length(long.data[[subject.name]]))
  za_e <- matrix(NA,BB,length(long.data[[subject.name]]))
  za <- matrix(NA,BB,length(long.data[[subject.name]]))
  
  etares <-vector(mode="list", length=maxit)
  mures <- matrix(NA,length(subjects)*d,maxit)
  psires <- matrix(NA,length(subjects)*d*(d+1)/2,maxit)
  betares <- matrix(NA,ncol(X),maxit)
  Gammares <- vector(mode="list", length=maxit)

  ## MM loop
  for(n in 1:maxit){
    for(s in 1:length(subjects)){
      #1.max
      op <- optim(x1[s,],Gs,control=list(fnscale=-1),method="L-BFGS-B", lower=c(-150),upper=c(150))
      par[s,] <- op$par
      conv[s] <- op$conv
      if(conv[s]!=0){stop("Optim dosent converge")}
      x1[s, ] <- par[s,]
      
      #estimate mu and psi
      mures[((s+((s-1)*d)-(s-1)):(d*s)),n] <- par[s,1:d]
      psires[(from2[s]:to2[s]),n] <- par[s,-(1:d)]
      
      #2. max
      mu <- par[s,1:d]
      psi <- par[s,-(1:d)]
      Psi <- matrix(Q%*%psi,d,d)
      
      alphas <- matrix(NA,d,BB*length(long.data$item[long.data[[subject.name]]==s]))
      for (i in 1:(BB*sum(long.data[[subject.name]]==s))){
        alphas[,i] <- mu + solve(Psi, rnorm(d))}
      
      zas <- matrix(NA,BB,sum(long.data[[subject.name]]==s))
      for (i in 1:sum(long.data[[subject.name]]==s)){
        zas[,i] <- (matrix(Zs[[s,1]],sum(long.data[[subject.name]]==s),ncol(Z)))[i,]%*%alphas[,(i*BB-(BB-1)):(i*BB)]}
      
      es <- matrix(NA,BB,sum(long.data[[subject.name]]==s))
      for (i in 1:(sum(long.data[[subject.name]]==s))){
        es[,i] <- rtruncnorm(1, a = mapply(function(x,y){x[y]},eta[long.data$item[long.data[[subject.name]]==s]],long.data$item.value[long.data[[subject.name]]==s])[i]-
                               (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta)[i]- zas[,i], 
                             
                             b = mapply(function(x,y){x[y+1]},eta[long.data$item[long.data[[subject.name]]==s]],long.data$item.value[long.data[[subject.name]]==s])[i]-
                               (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta)[i]-zas[,i])}
      
      za_e_s=zas+es
      
      ys <- matrix(NA,BB,sum(long.data[[subject.name]]==s))
      for (i in 1:(sum(long.data[[subject.name]]==s))){
        ys[,i] <- (matrix(Xs[[s,1]],sum(long.data[[subject.name]]==s),ncol(X))%*%beta)[i]+za_e_s[,i]}
      
      za[,from[s]:to[s]] <- zas
      y[,(from[s]:to[s])] <- ys
      za_e[,from[s]:to[s]] <- za_e_s
    }
    
    very.long.data <- full_join(long.data,tibble(rep=1:BB), by=character()) %>% 
      add_column(za_e=c(za_e), y=c(y),za=c(za))
    
    # estimate beta
    m1 <- lm(update(fixed,y~.+offset(za)),data=very.long.data)
    very.long.data$all_effects <- predict(m1)
    beta <- as.numeric(coef(m1))
    betares[,n] <- beta
    
    fun1 <- function(i){
      tmp <- clm(factor(item.value)~offset(all_effects),data=subset(very.long.data,item==i))$alpha
      names(tmp) <- NULL
      return(tmp)}
    
    # estimate eta
    eta <- lapply(items, fun1) 
    names(eta) <- items
    for (i in c(items.ordinal)){
      eta[[i]] <- append(eta[[i]],-Inf,after=0)
      eta[[i]] <- append(eta[[i]],Inf,after=length(eta[[i]]))}
    
    etares[[n]] <- eta
    
    # estimate Gamma
    Gamma <- chol(cov(t(alphas)))
    Gammares[[n]] <- append(Gammares[[n]],Gamma)
    
    # calculate the ELBO
    elb=0
    for (j in 1:length(subjects)){
      elb <- elb + ELBO(mu=c(mures[,n][((j+((j-1)*d)-(j-1)):(d*j))]),psi=c(psires[,n][(from2[j]:to2[j])]),beta=c(betares[,n]),eta=etares[[n]],Gamma=matrix(Gammares[[n]],d,d))
    }
    elbo[n] <- elb
    
    print(n)}

   res <- list(elbo=elbo,mu=c(mures[,maxit]),psi=c(psires[,maxit]),beta=c(betares[,maxit]),
              eta=etares[[maxit]],Gamma=matrix(Gammares[[maxit]],d,d))
  
   print(res)
   
   #plot of how the ELBO runs
   dfplot <- data.frame(x=c(1:maxit),y=elbo)
   p <- ggplot(dfplot, aes(x=x, y=y)) +
     geom_line()+xlab("Iterations")+
     ylab("ELBO")
   p
}
