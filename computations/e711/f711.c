// max over m in [0,lcm(1..n)) of f(n,m): minimal L s.t. distinct a_k in [m+1, m+L-1], k|a_k
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n; long long m; int L;
int matchA[100000]; int matchK[64]; int seen[100000]; int stamp;
int tryk(int k){
  long long a=(m/k+1)*k;
  for(;a<=m+L-1;a+=k){ int idx=(int)(a-m); if(seen[idx]==stamp) continue; seen[idx]=stamp;
    if(matchA[idx]==0 || tryk(matchA[idx])){ matchA[idx]=k; matchK[k]=idx; return 1;} }
  return 0;
}
int f(long long mm){
  m=mm; memset(matchK,0,sizeof(matchK)); L=n+1; for(int i=0;i<3*n*n+10;i++) matchA[i]=0;
  while(1){ int ok=1;
    for(int k=n;k>=1;k--){ if(matchK[k]) continue; stamp++; if(!tryk(k)){ok=0;break;} }
    if(ok) return L; L++; }
}
long long gcd(long long a,long long b){return b?gcd(b,a%b):a;}
int main(int argc,char**argv){
  int N=atoi(argv[1]);
  for(n=1;n<=N;n++){ long long l=1; for(int i=1;i<=n;i++) l=l/gcd(l,i)*i;
    int best=0; long long arg=0; int fnn=f(n);
    for(long long mm=0;mm<l;mm++){ int v=f(mm); if(v>best){best=v;arg=mm;} }
    printf("n=%d lcm=%lld f(n,n)=%d max_m f(n,m)=%d at m=%lld\n",n,l,fnn,best,arg); fflush(stdout);
  }
}
