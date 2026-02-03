// Parameters
q, v, d, o1, o2 := Explode([16,60,30,34,36]);


ComplexityPadded := function(q, v, d, o1, o2, l)
    nrows := l * (v + d + o1 + o2);
    ncols := d + o1 + o2;
    nvars := l * (v + d + o1);
    rank := o2;

    findb := function(mprime)
        mb1 := 0;
        nx := nvars;
        ny := Binomial(mprime, rank);
        
        final_b := 0;
        final_r := 0;

        for b in [1 .. rank + 2] do
            mb1 := Binomial(b + nx - 1, b) * ny;
            R := &+[ (-1)^(i+1) * Binomial(mprime, rank + i) * Binomial(nrows + i - 1, i) * Binomial(nvars + b - i - 1, b - i) : i in [1 .. b]];
            
            if R - mb1 + 1 gt 0 then
                final_b := b;
                // Complexity calculation: log2(3 * mb1^2 * (rank + 1) * nvars)
                final_r := Ceiling(Log(2, 3 * mb1^2 * (rank + 1) * nvars));
                break;
            end if;
        end for;
        return <final_b, final_r, mb1>;
    end function;

    goodchoice_mprime := 0;
    goodchoice_b := 0;
    min_bits := 100000;

    for mprime in [rank + 1 .. ncols] do
        res := findb(mprime);
        if res[2] lt min_bits then
            min_bits := res[2];
            goodchoice_mprime := mprime;
            goodchoice_b := res[1];
        end if;
    end for;

    print "*********************";
    print "number of layer:", l;
    print "mprime:", goodchoice_mprime;
    print "b:", goodchoice_b;
    print "bit operations:", min_bits;
    
    return min_bits;
end function;

ComplexitySimplePadded := function(q, v, d, o1, o2, l)
    nrows := l * (v + d + o1 + o2);
    ncols := d + o1 + o2;
    nvars := l * v;
    rank := o2;

    findb := function(mprime)
        mb1 := 0;
        nx := nvars;
        ny := Binomial(mprime, rank);
        
        final_b := 0;
        final_r := 0;

        for b in [1 .. rank + 2] do
            mb1 := Binomial(b + nx - 1, b) * ny;
            R := &+[ (-1)^(i+1) * Binomial(mprime, rank + i) * Binomial(nrows + i - 1, i) * Binomial(nvars + b - i - 1, b - i) : i in [1 .. b]];
            
            if R - mb1 + 1 gt 0 then
                final_b := b;
                // Complexity: log2((q/l) * 3 * mb1^2 * (rank + 1) * nvars)
                final_r := Ceiling(Log(2, (q/l) * 3 * mb1^2 * (rank + 1) * nvars));
                break;
            end if;
        end for;
        return <final_b, final_r, mb1>;
    end function;

    goodchoice_mprime := 0;
    goodchoice_b := 0;
    min_bits := 100000;

    for mprime in [rank + 1 .. ncols] do
        res := findb(mprime);
        if res[2] lt min_bits then
            min_bits := res[2];
            goodchoice_mprime := mprime;
            goodchoice_b := res[1];
        end if;
    end for;

    print "*********************";
    print "number of layer:", l;
    print "mprime:", goodchoice_mprime;
    print "b:", goodchoice_b;
    print "bit operations:", min_bits;
    
    return min_bits;
end function;

// Executions
print "Complexity of Padded Rectangular MinRank attack";
_ := ComplexityPadded(q, v, d, o1, o2, 1);
_ := ComplexityPadded(q, v, d, o1, o2, 2);
_ := ComplexityPadded(q, v, d, o1, o2, 3);

print "\nComplexity of Combined Simple Padded Rectangular MinRank attack";
_ := ComplexitySimplePadded(q, v, d, o1, o2, 1);
_ := ComplexitySimplePadded(q, v, d, o1, o2, 2);
_ := ComplexitySimplePadded(q, v, d, o1, o2, 3);