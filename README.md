# hyrax-bls12-381

## Introduction
This is a polynomial commitment implementation refer to [Hyrax](https://eprint.iacr.org/2017/1132.pdf) based on BLS12-381 implemented by [mcl](https://github.com/herumi/mcl). The underline operations of scalar and group element refers to OpenSSL.
This scheme is particularly for multi-linear extension of an array.

## Usage
First install mcl.

Then `cmake .` and `make` .

Test by `./src/hyrax_time`. The Hyrax PCS here supports multi-thread commitment. You can use this polynomial commitment in the following way:
```C++
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
    
    Fr eva=prover_evaluate(ww,r,l);  // this function needs optimization
    open(ww,r,eva,G,g,commit,l);  // commit is commitment, G,g is ecc bases, l is variable num
    
    t.stop("All time: ");
    return 0;
}
```

## Reference
- [Doubly-efficient zksnarks without trusted setup](https://doi.org/10.1109/SP.2018.00060). Wahby, R. S., Tzialla, I., Shelat, A., Thaler, J., & Walfish, M. (S&P 2018)

- [Hyrax](https://github.com/hyraxZK/hyraxZK.git)

- [mcl](https://github.com/herumi/mcl)
