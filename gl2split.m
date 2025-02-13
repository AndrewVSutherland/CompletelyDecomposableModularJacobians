/*
    Magma package associated to the paper "Completely decomposable modular Jacobians" by Jen Paulhus and Andrew V. Sutherland

    Depends on the packages utils,m, gl2base.m, gl2points.m available in https://github.com/AndrewVSutherland/Magma
*/

filter := func<H|GL2ContainsNegativeOne(H) and GL2DeterminantIndex(H) eq 1>;
msubs := func<r,N|[[sprint(h),sprint(H`Level),sprint(H`Index),"?",sprint(GL2Generators(GL2Project(H,H`Level)))] where h:=GL2GassmannHash(H) where H:=K`subgroup : K in MaximalSubgroups(GL2Lift(GL2FromGenerators(r[2],r[3],r[5]),N)) | filter(K`subgroup)]>;
splitkeys := func<S,N,Q,M,I,J|[[r[1],itoa(Integers()!&+Eltseq(v))]:r in S | &and[v[i] ge 0 and Denominator(v[i]) eq 1:i in [1..Degree(v)]] and ChangeRing(v,Integers())*J eq w and &+Eltseq(v) eq GL2Genus(H)
                                where v := Vector(Rationals(),t[1..n])*I where w := Vector(Integers(),t[n+1..#Q]) where t:=GL2Traces(GL2Lift(H,N),Q,M) where H:=GL2FromGenerators(r[2],r[3],r[5])] where n:=NumberOfRows(I)>;
zpad := func<n,d|&cat[Parent("")|"0":i in [1..(d-#s)]] cat s where s:=IntegerToString(n)>;

intrinsic TracesOfFrobenius(S::SeqEnum[CrvEll],B::RngIntElt) -> SeqEnum[SeqEnum[RngInt]]
{ Given a sequence of elliptic curve E/Q and a bound B, returns a corresponding list of Frobenius traces at p <= B. }
    jobfile := Tempname("magmajob"); jobsfile := Tempname("magmajobs"); outfile := Tempname("traces");
    Puts(Open(jobfile,"w"),Sprintf("print n cat \":\" cat sprint(TracesOfFrobenius(EllipticCurve(atoii(E)),%o)); exit;",B));
    fp := Open(jobsfile,"w");
    for i:=1 to #S do Puts(fp,Sprintf("magma -b n:=%o E:=%o %o",i,sprint(Eltseq(S[i])),jobfile)); end for; Flush(fp);
    System(Sprintf("parallel <%o | sort -t: -k1,1n | awk -F: '{print $2}' >%o",jobsfile,outfile));
    T := Split(Read(outfile));
    System(Sprintf("rm %o %o %o",jobfile,jobsfile,outfile));
    return [atoii(r):r in T];
end intrinsic;

intrinsic InvertibleTraceMatrix(T::SeqEnum[SeqEnum[RngIntElt]],N::RngIntElt) -> AlgMatElt[FldRat], SeqEnum[RngIntElt]
{ Given a list T of lists of Frobenius traces at all primes p <= B (for some B) and an integer N, computes an invertible #T x #T matrix M and a list of primes p not dividing N corresponding to columns of M.  An error will occur if the lists of Frobenius traces at p not dividing N are not linearly independent. }
    B := NthPrime(#T[1]);  Q := PrimesUpTo(B);
    M := []; I := [Integers()|];
    J := [i:i in [1..#Q]|N mod Q[i] ne 0];
    b := 64;
    while true do
        m := Min(#J,b); assert m gt 0;
        r := Rank(Matrix([t[I cat J[1..m]]:t in T]));
        if r eq #I + m then
            I cat:= J[1..m]; J := J[m+1..#J];
            if #I eq #T then break; end if;
            if b lt 64 then b*:= 2; end if;
            continue;
        end if;
        if r eq #I then J := J[m+1..#J]; if b lt 64 then b*:= 2; end if; continue; end if;
        b div:= 2;
    end while;
    M := Matrix(Rationals(),[t[I]:t in T]); assert Rank(M) eq #T;
    return M, Q[I]; // if v is a row vector encoding a linear combination x of Frobenius traces at p in Q then v*M = x, and v = x*M^-1 lets us recover v from the linear combination
end intrinsic;

intrinsic GL2SplitLattice(N::RngIntElt:threads:=1,extra:=10)
{ Enumerates the subgroup lattice of GL(2,Z/NZ) consisting of H containing -1 with surjective determinant for which J_H appears to be completely decomposable, writing results of positive genus to gl2smin_N.txt in the format level:index:genus:generators.  While the output file is guaranteed to contain every completely decomposable J_H, it may contain some that are not. }
    require N gt 0: "N must be a positive integer";
    require threads gt 0 and threads lt 1000: "threads should be a positive integer less than 1000";
    rstart := Realtime(); cstart := Cputime();
    EE := EllipticCurvesOfConductorDividing(N^2);
    if #EE eq 0 then printf "There are no completely decomposable J_H of level dividing %o with positive genus.\n", N; return; end if;
    vprintf GL2,1: "Found %o elliptic curve isogeny classes of conductor dividing %o in %.3os\n", #EE, N, Realtime()-rstart;
    badp := PrimeDivisors(N); badi := [#PrimesUpTo(p):p in badp];
    vprintf GL2,2: "Computing Frobenius trace matrix for %o E/Q of full rank...\n", #EE; rt := Realtime();
    B := NthPrime(#EE+extra+#badp); repeat B := Ceiling(1.3*B);  T := TracesOfFrobenius(EE,B); I:=[i:i in [1..#T[1]]|not i in badi]; until Rank(Matrix([t[I]:t in T])) ge #EE;
    vprintf GL2,1: "Computed %o x %o trace matrix in %.3os\n", #T, #T[1], Realtime()-rt; rt := Realtime();
    I,Q := InvertibleTraceMatrix(T,N);
    vprintf GL2,1: "Computed invertible %o x %o trace matrix in %.3os\n", #T, #T, Realtime()-rt; rt := Realtime();
    I := I^-1;
    vprintf GL2,1: "Inverted invertible %o x %o trace matrix in %.3os\n", #T, #T, Realtime()-rt; rt := Realtime();
    P := PrimesUpTo(B);
    while true do
        i:= #PrimesUpTo(Q[#Q])+1; pi := []; while #pi lt extra and i le #T[1] do if N mod P[i] ne 0 then Append(~pi,i); end if; i +:= 1; end while;
        if #pi eq extra then break; end if;
        B := Ceiling(1.1*B); P := PrimesUpTo(B); T := TracesOfFrobenius(EE,B);
    end while;
    Q cat:= P[pi]; J := Matrix(Integers(),[[T[i][j]:j in pi]:i in [1..#T]]); delete pi;
    M := GL2PointCountsPrecompute(N,Q);
    vprintf GL2,1: "Precomputed point-counting matrix for N=%o at %o primes in %.3os\n", #T, #T[1], Realtime()-rt; rt := Realtime();
    pslist:=[];
    if N ge 50 then
        D := [M:M in Divisors(N)|M ge 50];
        for M in D do _ := GL2SavePrimitiveSimilarityIndexes(M); end for;
    end if;
    vprintf GL2,1: "Setup for level %o with %o elliptic curve candidates took %.3os\n", N, #Q, Realtime()-rstart;
    L := [[sprint(GL2GassmannHash(GL2Ambient(1))),"1","1","0","[]"]]; X := Set(L);
    level := 0; file1 := Tempname("SplitLattice1_"); file2 := Tempname("SplitLattice2_");
    while #L gt 0 do
        vprintf GL2,2: "Computing maximal subroups of %o groups in layer %o using %o threads...\n", #L, level, threads; rt := Realtime(); ct := Cputime();
        m := Min(#L,threads);
        for tid in [1..m] do if Fork() eq 0 then
            S := &cat[msubs(L[i],N):i in [tid..#L by m]];
            putrecs(Sprintf("%o_%o",file1,tid),S);
            exit;
        end if; end for; WaitForAllChildren();
        mcnt := atoi(Split(Pipe(Sprintf("cat %o_* | wc -l",file1),"")," ")[1]);
        if mcnt eq 0 then break; end if;
        vprintf GL2,1: "Computed %o maximal subgroups of %o groups in layer %o using %o threads in %.3os (%.3os/group)\n", mcnt, #L, level, threads, Realtime()-rt, (Cputime()-ct)/#L;
        System(Sprintf("cat %o_* > %o ; rm %o_* ; sort -t: -u -k1,1 %o > %o",file1,file1,file1,file1,file2,threads));
        gcnt := atoi(Split(Pipe(Sprintf("cat %o* | wc -l",file2),"")," ")[1]);
        m := Min(gcnt,threads);
        System(Sprintf("split -n r/%o -d -a 3 %o %o ; rm %o",m,file2,file2,file2));
        level +:= 1;
        vprintf GL2,2: "Testing %o Gassmann reps of %o subgroups in layer %o for complete decomposibility using %o threads...\n", gcnt, mcnt, level, threads; rt := Realtime(); ct := Cputime();
        for tid in [1..m] do if Fork() eq 0 then
            S := getrecs(file2 cat zpad(tid-1,3));
            T := splitkeys(S,N,Q,M,I,J);
            putrecs(Sprintf("%o_%o",file2,tid),T);
            exit;
        end if; end for; WaitForAllChildren();
        S := Split(Read(file1)); System(Sprintf("rm %o ; cat %o_* > %o ; rm %o*",file1,file2,file1,file2));
        T := getrecs(file1); scnt := #T; Z := AssociativeArray(); for r in T do Z[r[1]] := r[2]; end for;
        fp := Open(file1,"w"); scnt := 0; for s in S do if IsDefined(Z,s[1..Index(s,":")-1]) then r:=Split(s,":"); r[4]:=Z[r[1]]; Puts(fp,Join(r,":")); scnt +:=1; end if; end for; Flush(fp); delete fp; delete S; delete T; delete Z;
        vprintf GL2,1: "Found %o of %o completely decomposable candidates in %o of %o Gassmann classes in layer %o using %o threads in %.3os (%.3os/class) seconds\n", scnt, mcnt, #X, gcnt, level, threads, Realtime()-rt, (Cputime()-ct)/gcnt;
        if scnt eq 0 then break; end if;
        m := Min(scnt,threads);
        System(Sprintf("split -n r/%o -d -a 3 %o %o ; rm %o", m,file1,file1,file1));
        vprintf GL2,2: "Canonicalizing %o subgroups in layer %o using %o threads...\n", scnt, level, threads; rt := Realtime(); ct := Cputime(); 
        for tid in [1..m] do if Fork() eq 0 then
            S := getrecs(file1 cat zpad(tid-1,3));
            fp := Open(Sprintf("%o_%o",file1,tid),"w");for r in S do H:=GL2Canonicalize(GL2FromGenerators(r[2],r[3],r[5])); Puts(fp,Sprintf("%o:%o:%o:%o:%o", r[1], r[2], r[3], r[4], sprint(GL2Generators(H)))); end for; Flush(fp); delete fp;
            exit;
        end if; end for; WaitForAllChildren();
        vprintf GL2,1: "Computed canonical generators for %o subgroups in layer %o using %o threads in %.3os (%.3o/group)\n", scnt, level, threads, Realtime()-rt, (Cputime()-ct)/scnt;
        vprintf GL2,2: "Removing duplicates among %o subgroups in layer %o using 1 thread...\n", scnt,level;  ct := Cputime(); rt := Realtime();
        System(Sprintf("cat %o_* > %o ; rm %o*",file1,file2,file1));
        S := getrecs(file2); L := []; for r in S do if not r in X then Include(~X,r); Append(~L,r); end if; end for; delete S;
        vprintf GL2,2: "Added %o new candidate completely decomposable subgroups in layer %o yielding total of %o using 1 thread in %.3os (%.3o/grouip)\n", #L, level, #X, Realtime()-rt, (Cputime()-ct)/#L;
    end while;
    vprintf GL2,2: "Writing and sorting %o candidate completely decomposable subgroups for N=%o using 1 thread...\n", #X,N; rt := Realtime(); ct := Cputime();
    fp := Open(file1,"w"); for r in X do if r[4] ne "0" then Puts(fp,Join(r[2..#r],":")); end if; end for; Flush(fp); delete fp;
    System(Sprintf("sort -t: -k2,2n -k3,3n -k4,4n -k1,1n -k5,5 %o > %o ; rm -f %o* %o*",file1,Sprintf("gl2smin_%o.txt",N),file1,file2));
    printf "Wrote %o candidate completely decomposable subgroups for N=%o to output file gl2smin_%o.txt in %.3os seconds, total elapsed time %.3os (%.3os/group)\n",#X,N,N,Realtime()-rt,Realtime()-rstart,(Cputime()-cstart)/#X;
end intrinsic;

intrinsic GL2CMFSpacesNeeded(N::RngIntElt) -> SeqEnum[MonStgElt]
{ Returns a list of labels of weight 2 newspaces of positive dimension that contain all of the newform orbits f for which the modular abelian variety A_f appears in the isogeny decomposition of Jac(X_H) for some H of level N (and genus g <= GenusBound if GenusBound is nonzero). }
    S := &cat[[CharacterOrbitLabel(s):s in ConreyCharacterOrbitReps(M:ConductorDivides:=N,ParityEquals:=1)]:M in Divisors(N^2)];
    S := [s:s in S|DimensionNewCuspForms(DirichletCharacter(s),2) gt 0];
    return [a[1] cat ".2." cat a[2] where a:=Split(s,"."):s in S];
end intrinsic;

intrinsic GL2LoadCMFTraces(filename::MonStgElt,N::RngIntElt) -> SeqEnum[MonStgElt], SeqEnum[SeqEnum[RngIntElt]]
{ Loads CMF data from the specified file sufficient to decompose the Jacobian of X_H of level N (and verifies that all the necessary data is present). Returns a list of CMF labels and a corresponding list of traces. }
    S := Split(Read(filename));
    X := Set(GL2CMFSpacesNeeded(N));
    T := [Split(r,":"):r in S|Join(Split(r[1..Index(r,":")-1],".")[1..3],".") in X];
    D := [atoi(r[4]):r in T];
    require &+D eq &+[DimensionNewCuspForms(chi,2)*Degree(chi) where chi:=DirichletCharacter(Join(Split(k,".")[[1,3]],".")):k in X]: Sprintf("Not all of the forms needed for level %o are present in the file %o!",N,filename);
    F := [r[1]:r in T];  T := [atoii(r[8]):r in T];
    B := NthPrime(Min([#t:t in T])); P := PrimesUpTo(B); I := [i:i in [1..#P]|N mod P[i] ne 0];
    require Rank(Matrix([t[I]:t in T])) eq #T: Sprintf("Trace matrix of %o CMFs needed for level %o at primes up to %o coprime to the level is not invertible, you need more traces!",#T,N,B);
    return T,D,F;
end intrinsic;

intrinsic GL2SplitVerify(grpfile::MonStgElt,cmffile::MonStgElt:threads:=1) -> BoolElt
{ Reads records from grpfile in the format level:index:genus:generators define a subgroup H and rigorously verifies that J_H is completely decomposable using modular form data in cmffile (which should contain the trace form for every eigenform in S_2(Gamma1(N) cap Gamma_0(N^2)) and enough aps to ensure linear independence). }
    rstart := Realtime(); cstart := Cputime();
    S := Split(Read(grpfile));
    Ns := { atoi(s[1..Index(s,":")-1]):s in S};
    vprintf GL2,1: "Precomputing data for levels in %o...\n", Ns;
    A := AssociativeArray();
    for N in Ns do
        t := Cputime();
        A[N] := <Q,M,I,D,F> where I:= J^-1 where M:=GL2PointCountsPrecompute(N,Q) where J,Q:=InvertibleTraceMatrix(T,N) where T,D,F := GL2LoadCMFTraces(cmffile,N);
        vprintf GL2,1: "Precomputed invertible trace matrix and point-counting matrix for level %o in %.3os\n", N, Cputime()-t;
    end for;
    errcnt := 0;
    for tid in [1..Min(threads,#S)] do if Fork() eq 0 then
        for i:=tid to #S by threads do
            t := Cputime();
            r := Split(S[i],":"); N := atoi(r[1]);
            H := GL2FromGenerators(r[1],r[2],r[4]);
            v := Vector(Rationals(),GL2Traces(H,A[N][1],A[N][2]))*A[N][3];
            assert &and[v[i] ge 0 and Denominator(v[i]) eq 1:i in [1..Degree(v)]];
            assert &+[v[i]*A[N][4][i]:i in [1..Degree(v)]] eq atoi(r[3]);
            if {A[N][4][i]:i in [1..Degree(v)]|v[i] gt 0} ne {1} then
                print "Verification failed for record",S[i];
                print "Computed decomposition is", {*A[N][4][i]^^v[i]:i in [1..Degree(v)]*};
                errcnt +:= 1; 
            else
                vprintf GL2,2: "Verified %o is completely decomposible in %.3os\n", S[i], Cputime()-t;
            end if;
        end for;
    end if; end for; WaitForAllChildren();
    if errcnt gt 0 then error Sprintf("Verification failed for %o records in %o\n", errcnt, grpfile); return false; end if;
    vprintf GL2,2: "Verified %o of %o groups are completely decomposible in %.3os (%.3o CPU s)\n", #S, #S, Cputime()-rstart, Cputime()-cstart;
    return true;
end intrinsic;
