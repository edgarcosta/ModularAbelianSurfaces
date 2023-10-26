AttachSpec("~/projects/CHIMP/CHIMP.spec");
AttachSpec("~/projects/ModularAbelianSurfaces/spec");

SetNthreads(1);

s := Split(input, ":");
label := s[1];
prec := StringToInteger(prec);
SetDefaultRealField(RealField(prec));
start := Time();
try
f := LMFDBNewform(label : labelswithhecke := "data/3.3.49.1.txt");
t := RealTamagawaNumber(f);
mb := Sprintf("%.2o", GetMaximumMemoryUsage()*1.0*2^-20);
wt := Time(start);
catch er
  WriteStderr(er);
  exit 1;
end try;
StripWhiteSpace(Join([label, Sprint(t), mb, wt], ":"));
exit 0;
