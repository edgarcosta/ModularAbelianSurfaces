AttachSpec("~/GitHub/CHIMP/CHIMP.spec");
AttachSpec("/Users/aashrayajha/Documents/GitHub/ModularAbelianSurfaces/spec");

datafile := "/Users/aashrayajha/Documents/GitHub/ModularAbelianSurfaces/examples/NS25/625.2.a.period-data.dat";
data := ReadObject(Open(datafile, "r"));

labels, prec, curves, PeriodsC, PiC, PeriodsM, PeriodsMTransformed, PiM, Isogs, homs := Explode(data);

printf "Loaded %o\n", datafile;
printf "#homs = %o\n", #homs;
