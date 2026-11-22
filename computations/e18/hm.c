// Erdos #18: h(m) for m = n!, h(m)=max_{1<=k<m} min number of distinct divisors of m summing to k
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc,char**argv){
  int n=atoi(argv[1]); uint64_t m=strtoull(argv[1],0,10);
  uint64_t *d=malloc(sizeof(uint64_t)*20000); int nd=0;
  for(uint64_t a=1;a*a<=m;a++) if(m%a==0){d[nd++]=a; if(a*a!=m) d[nd++]=m/a;}
  // sort ascending
  for(int i=0;i<nd;i++)for(int j=i+1;j<nd;j++)if(d[j]<d[i]){uint64_t t=d[i];d[i]=d[j];d[j]=t;}
  uint8_t *dp=malloc(m); memset(dp,255,m); dp[0]=0;
  uint64_t reach=0; // max reachable sum so far (sum of divisors processed)
  for(int i=0;i<nd;i++){ uint64_t x=d[i]; if(x>=m) continue;
    uint64_t top=reach+x; if(top>m-1) top=m-1;
    for(uint64_t s=top; s>=x; s--){ uint8_t c=dp[s-x]; if(c!=255 && c+1<dp[s]) dp[s]=c+1; if(s==x)break;}
    reach+=x;
  }
  int h=0; uint64_t arg=0, bad=0;
  for(uint64_t k=1;k<m;k++){ if(dp[k]==255){bad++;continue;} if(dp[k]>h){h=dp[k];arg=k;} }
  printf("n=%d m=%llu divisors=%d h(m)=%d (first k attaining: %llu) unreachable=%llu\n",n,(unsigned long long)m,nd,h,(unsigned long long)arg,(unsigned long long)bad);
  return 0;
}
