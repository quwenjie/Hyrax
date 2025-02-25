#undef NDEBUG
#include "hyrax.hpp"
#include <cmath>
using namespace std;
using namespace mcl::bn;

const int MAX_MSM_LEN=1e4;
const int COMM_OPT_MAX=65536; //don't optimize if larger than this
const int logmax=16;  /// max number=2^18-1
const int block_num=4;  //2^80


G1 perdersen_commit(G1* g,ll* f,int n,G1* W)
{
    G1 ret;
    ret.clear();
    
    bool *used=new bool[COMM_OPT_MAX*block_num];
    memset(used,0,sizeof(bool)*COMM_OPT_MAX*block_num);
    ll bar[10];
    ll bar_t=1;
    for(int i=0;i<8;i++)
    {
        bar[i]=bar_t;
        bar_t<<=logmax;
    }
    for(int i=0;i<n;i++)
    {
            if(f[i]==0)
                continue;
            
            if(f[i]<0)
            {
                ll tmp=-f[i];
                for(int j=0;j<block_num;j++)
                {
                    if(tmp<bar[j])
                        break;
                    ll fnow=(tmp>>(logmax*j))&65535;
                    W[fnow+(j<<logmax)]-=g[i];
                    used[fnow+(j<<logmax)]=1;
                }
            }
            else
            {
                ll tmp=f[i];
                for(int j=0;j<block_num;j++)
                {
                    if(tmp<bar[j])
                        break;
                    ll fnow=(tmp>>(logmax*j))&65535;
                    W[fnow+(j<<logmax)]+=g[i];
                    used[fnow+(j<<logmax)]=1;
                }
            }
    }
    G1 gg[logmax*block_num];
    for(int j=0;j<logmax*block_num;j++)
        gg[j].clear();
    for(int j=0;j<COMM_OPT_MAX*block_num;j++)
    {
        if(used[j])
        {
            int jj=j%COMM_OPT_MAX;
            int blk=j/COMM_OPT_MAX;
            for(int k=0;k<logmax;k++)
            {
                if(jj&(1<<k))
                    gg[k+logmax*blk]+=W[j];
            }
            W[j].clear();
            used[j]=0;            
        }
    }
    for(int j=0;j<logmax*block_num;j++)
    {
        if(j>60)
        {
            G1 gd=gg[j]*(1ll<<48);
            ret+=gd*(1ll<<(j-48)); //split
        }
        else
            ret+=gg[j]*(1ll<<j);
    }
    delete []used;
    return ret;
}



G1 perdersen_commit(G1* g,Fr* f,int n)
{
    G1 ret;
    G1::mulVec(ret,g,f,n);
    return ret;
}

Fr lagrange(Fr *r,int l,int k)
{
    assert(k>=0 && k<(1<<l));
    Fr ret=1;
    for(int i=0;i<l;i++)
    {
        if(k&(1<<i))
            ret*=r[i];
        else
            ret*=1-r[i];
    }
    return ret;
}


G1 gen_gi(G1* g,int n)
{
    G1 base;
    base.setStr("1 0x2523648240000001ba344d80000000086121000000000013a700000000000012 0x1");
    
    for(int i=0;i<n;i++)
    {
        Fr tmp;
        tmp.setByCSPRNG();
        g[i]=base*tmp;
    }
    return base;
}


Pack bullet_reduce(G1 gamma, Fr*a,Fr* x,Fr y,G1*g,G1& G,int n,bool need_free) // length n
{
    if(n==1)
    {
        Pack p(gamma,a[0],g[0],x[0],y);
        return p;
    }
    
    //step2  prover fold
    G1 gamma_minus1,gamma_1;
    Fr x1a2=0,x2a1=0;
    for(int i=0;i<n/2;i++)
    {
        x1a2+=x[i]*a[n/2+i];
        x2a1+=x[n/2+i]*a[i];
    }
    gamma_minus1=G*x1a2+perdersen_commit(g+n/2,x,n/2);
    gamma_1=G*x2a1+perdersen_commit(g,x+n/2,n/2);
    Fr c,invc;
    c.setByCSPRNG();  // step3 V choose random c
    Fr::inv(invc,c);

    
    G1 gamma_prime=gamma_minus1*c*c+gamma_1*invc*invc+gamma;
    Fr* aprime=new Fr[n/2];       
    for(int i=0;i<n/2;i++)
        aprime[i]=a[i]*invc+a[i+n/2]*c;
    G1* gprime=new G1[n/2];           
    for(int i=0;i<n/2;i++)
        gprime[i]=g[i]*invc+g[i+n/2]*c;
    

    Fr* xprime=new Fr[n/2];         
    Fr yprime;
    for(int i=0;i<n/2;i++)
        xprime[i]=c*x[i]+invc*x[i+n/2];
    yprime=c*c*x1a2+invc*invc*x2a1+y;
    //P.stop("Bullet proof Part3 fold x & y",false);
    if(need_free)
    {
        delete []a;
        delete []g;
        delete []x;
    }
    
    return bullet_reduce(gamma_prime,aprime,xprime,yprime,gprime,G,n/2,true);
}   

bool prove_dot_product(G1 comm_x, G1 comm_y, Fr* a, Fr* x,Fr y,G1*g , G1& G,int n)  // y= <a,x> , 
{
    G1 gamma=comm_x+comm_y;
    timer blt;
    blt.start();
    Pack p=bullet_reduce(gamma,a,x,y,g,G,n,false);
    assert(p.y==p.x*p.a);
    assert(p.gamma==p.g*p.x+G*p.y);
    blt.stop("bullet reduce ");
    return true;
    
}
static ThreadSafeQueue<int> workerq,endq;


void ll_commit_worker(G1*& Tk,G1*& g, ll*& w,int rownum,int colnum,G1*& W)
{
    int idx;
    while (true)
    {
            bool ret=workerq.TryPop(idx);
            if(ret==false)
                return;
            
            Tk[idx].clear();
            for(int i=0;i<colnum;i++)
                Tk[idx]+=g[i]*Fr(w[i*rownum+idx]);
            endq.Push(idx);
    }
}
G1* prover_commit(ll* w, G1* g, int l,int thread_n) //compute Tk, int version with pippenger
{
    cerr<<"dog "<<thread_n<<endl;
    //w has 2^l length
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<(l-halfl));
    G1 *Tk=new G1[rownum];
    timer t;
    t.start();
    G1** W=new G1*[thread_n];

    for(int i=0;i<thread_n;i++)
        W[i]=new G1[COMM_OPT_MAX*block_num];

    for(int i=0;i<thread_n;i++)
        memset(W[i],0,sizeof(G1)*COMM_OPT_MAX*block_num);
    for (u64 i = 0; i < rownum; ++i)  //work for rownum 
        workerq.Push(i);

    for(int i=0;i<thread_n;i++)
    {
        thread t(ll_commit_worker,std::ref(Tk),std::ref(g),std::ref(w),rownum,colnum,std::ref(W[i])); 
        t.detach();
    }
    while(!workerq.Empty())
        this_thread::sleep_for (std::chrono::microseconds(10));
    while(endq.Size()!=rownum)
        this_thread::sleep_for (std::chrono::microseconds(10));
    endq.Clear();
    assert(endq.Size()==0);
    t.stop("commit time(PPG) ");
    for(int i=0;i<thread_n;i++)
        delete [] W[i];
    delete []W;
    return Tk;
}


Fr* get_eq(Fr*r, int l)
{
    Fr* eq=new Fr[1<<l];
    eq[0]=1-r[0];
    eq[1]=r[0];
    for(int i=2;i<=l;i++)
    {
        for(int j=(1<<i)-1;j>=0;j--)
        {
            if(j&(1<<(i-1)))
                eq[j]=eq[j-(1<<(i-1))]*r[i-1];
            else
                eq[j]=eq[j]*(1-r[i-1]);
        }
    }
    return eq;
}
Fr prover_evaluate(ll*ww ,Fr*r, int l)  // nlogn brute force 
{
    timer t(true);
    t.start();
    Fr eval=0;
    Fr* lag=get_eq(r,l);
    for(int k=0;k<(1<<l);k++)
        eval+=lag[k]*Fr(ww[k]);
    t.stop("eval total ",true,false);
    return eval;
}

void open(ll*w,Fr*r,Fr eval,G1&G,G1*g,G1*comm,int l)
{
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<(l-halfl));
    timer verf;
    Fr*L=get_eq(r,halfl);
    Fr*R=get_eq(r+halfl,l-halfl);
    verf.start();
    Fr* LT=new Fr[colnum];
    for(int i=0;i<colnum;i++)
        LT[i]=0;
    for(int j=0;j<rownum;j++)
    for(int i=0;i<colnum;i++)
    {
        LT[i]+=L[j]*Fr(w[j+i*rownum]);   // mat mult  (1,row)*(row,col)=(1,col)
    }

    G1 tprime=perdersen_commit(comm,L,rownum); //random combine comm
    prove_dot_product(tprime, G*eval, R, LT,eval,g , G,colnum);
    verf.stop("total verify :");
}
