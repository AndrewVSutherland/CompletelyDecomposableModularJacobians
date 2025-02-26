# CompletelyDecomposableModularJacobians
Code and data associated to the paper "Completely decomposable modular Jacobians" by Jen Paulhus and Andrew V. Sutherland

## Data

The file `examples.txt` contains details about each of the 84 modular curves X_H listed in Table 1 of the paper.  The file contains lines of the form
```
  N:i:g:gens:label:[ec1,ec2,...]
```
where
- `N` is the level of H.
- `i` is the index of H.
- `g` is the genus of H.
- `gens` is a list of quadruples defining generators for the projection of H to GL(2,Z/NZ).
- `label` is the LMFDB label of X_H if known (otherwise it will be `?`).
- `[ec1,ec2,...]` is a list of g LMFDB labels of isogeny classes of elliptic curves that appear as isogeny factors of J_H.

The file `grpdata.txt` contains information about the 561,077 open subgroups H of GL(2,Zhat) of with surjective determinant containing -I of level less than 240 for which J_H is completely decomposable (including the 83 groups in `examples.txt` with positive genus).  It's records have the same format as examples.txt except the list of isogeny class labels at the end is omitted to save space (this list can be easily recomputed for any particular group using the function `GL2IsCompletelyDecomposable`, see below).

The files `cmfdata_N.txt` contain modular form data sufficient to rigorously verify the decomposition of J_H for H of level N; it includes a complete list of traceforms associated to Galois orbits of all weight 2 newforms f of level dividing N^2 with character of conductor dividing N.  As proved in [RSZB22](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/ell-adic-images-of-galois-for-elliptic-curves-over-mathbb-q-and-an-appendix-with-john-voight/D5BC92F9949B387570A7D764635B6AC8), for H of level N, the isogeny decompostion of J_H consists entirely of modular abelian varieties A_f associated to such newforms f.  There are files for each of the levels N = 6,7,10,11,15,18,20,24,28,30,36,48,60,120, which suffices to verify all the examples in `examples.txt`.

## Code

This code depends on various Magma packages in the GitHub repository [AndrewVSutherland/Magma](https://github.com/AndrewVSutherland/Magma) which is included in this repository as a submodule (so you do not need to clone/download it separately).

Magma Version 2.28-19 or later is recommended, and version 2.28-5 or later is required (if you use a version prior to 2.28-19 your should start magma using `magma -b` to suppress the banner, otherwise you will see spurious informational messages).

The package file [gl2split.m](https://github.com/AndrewVSutherland/CompletelyDecomposableModularJacobians/blob/main/gl2split.m) implements two intrinsics of note: `GL2SplitLattice` and `GL2SplitVerify`.  The function `GL2SplitLattice` implements the algorithm described in the paper to search for completely decomposable modular Jaocbians of a specified level N and generates an output file `gl2smin_N.txt` with the same format as `grpdata.txt` with the final `label` column omitted.  It also takes an optional parameter `threads`.  The default is 1 thread, which is fine for small N, but for larger N the computations will complete much more quickly using a larger number of threads (the computations described in the paper all used 360 threads running on a 360 vCPU machine, and even with this many threads, level 120 takes several days to complete).

The function `GL2SplitVerify` rigorously verifies the results of `GL2SplitLattice` for a given value of N.  This can be used to verify all the examples in `examples.txt` in a reasonable short amount of time (around 5 minutes using 1 thread on a fast machine).  To perform this verification, clone this repo to a machine with Magma version 2.28-5 or later installed and run:
```
$ magma -b
> AttachSpec("spec");
> for N in [7,10,11,15,18,20,24,28,30,36,48,60,120] do print N,GL2SplitVerify("examples.txt",N); end for;
7 true
10 true
11 true
...
```
This should take 5-10 minutes (almost all of which will be spent on level 120).  Note that no verification is required for N <= 6 because the genus of curves at these levels is bounded by 1.

To recompute the all the groups in `grpdata.txt` of level N use
```
$ magma -b
> AttachSpec("spec");
> N := 15; // or any level N you like
> n := 8;  // how many cores to use
> GL2SplitLattice(N:threads:=n);
Wrote 101 candidate completely decomposable subgroups for N=15 to output file 
gl2smin_15.txt in 0.010s seconds, total elapsed time 1.540s (0.080s/group)
```
with `n` set to the number of cores or hyperthreads you have available on your machine.

To see more details about either computation as it is being run type
```
SetVerbose("GL2",1);
```
before calling `GL2SplitVerify` or `GL2SplitLattice`.

To compute the list of elliptic curve isogeny classes in the decomposition of J_H for a particular H in GL(2,Z/NZ), including but not limited to any of the H listed in `grpdata.txt`, you can use the function `GL2IsCompletelyDecomposable`.  For example
```
$ magma -b
> AttachSpec("spec");
> S := getrecs("grpdata.txt");
> r := S[#S]; // or any particular record in S
> GL2IsCompletelyDecomposable(GL2FromGenerators(r[1],r[2],r[4]));
true [ 14.a, 28322.c, 56644.q, 56644.q ]
```
