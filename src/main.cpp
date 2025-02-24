//
// Created by juzix on 2021/6/17.
//
#undef NDEBUG
#include <mcl/bn256.hpp>
#include <iostream>
#include "hyrax.hpp"
using namespace std;

using namespace mcl::bn;


const int MAXL=23;  // only supports even, need debug
ll ww[(1<<MAXL)];


Fr r[MAXL];
G1 g[1<<(MAXL/2)];

void field(const char* f,Fr x)
{
    if(x.isNegative())
        cout<<f<<" -"<<-x<<endl;
    else
        cout<<f<<" "<<x<<endl;
    
}
int main(int argc, char *argv[])
{

    initPairing(mcl::BN254);

    int l=MAXL;
    for(int i=0;i<(1<<l)-8;i++)
    {
        ww[i]=1ll*(rand()%10000000-5000000);

    }
    for(int i=(1<<l)-12;i<(1<<l);i++)
    {
        if(i&1)
            ww[i]=1ll<<54;
        else    
            ww[i]=(1ll<<54)-i;
   
    }
    
    for(int i=0;i<l;i++)
        r[i].setByCSPRNG();

    G1 G=gen_gi(g,1<<(l-l/2)); //pedersen group

    timer t;
    t.start();

    G1* commit=prover_commit(ww,g,l,16);  // supports pippenger and multi-thread commit
    //ww[100]-=1;
    Fr eva=prover_evaluate(ww,r,l);  // this function needs optimization
    open(ww,r,eva,G,g,commit,l);  // tprime, comm_w ,R,g,G public, LT eval only prover knows
    
    t.stop("All time: ");
    return 0;
}


//TODO: long long 1x slower than int, should optimize