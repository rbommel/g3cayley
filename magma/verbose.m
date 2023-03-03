declare verbose G3Cayley, 2;

/* Indented bench functions */

declare verbose G3CayleyIndents, 1000000000;

function MyBenchIndent(type : indent := 3)

    n := GetVerbose("G3CayleyIndents");

    if type eq "-" then n -:= indent;  end if;

    idtstr :=  n gt 0 select &*[" " : i in [1..n]] else "";

    if type eq "+" then n +:= indent; end if;

    SetVerbose("G3CayleyIndents", n);

    return idtstr;
end function;

function MyBenchStart(lvl, str : indent := 3)

    vprintf G3Cayley, lvl : "%oComputing %o...\n", MyBenchIndent("+" : indent := indent), str;

    return Cputime();

end function;

procedure MyBenchStop(lvl, str, tt : indent := 3)

    vprintf G3Cayley, lvl : "%o... %o computed in %.2o s\n", MyBenchIndent("-" : indent := indent), str, Cputime(tt);

end procedure;
