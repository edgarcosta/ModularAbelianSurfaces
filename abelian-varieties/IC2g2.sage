# Sage functions to compute genus 2 curves using a simplification of the
# Mestre conic and cubic in terms of Igusa-Clebsch invariants 
# 
# WARNING : this is a preliminary implementation and only treats
# 	construction of genus 2 curves which can be defined over Q
#	such that the reduced automorphism group has odd order
#
# Kimball Martin - April 2022

# return the IC-simplified Mestre conic
def ICmestre(ICs):
  (I2, I4, I6, I10) = ICs
  return matrix([(-3*I2^3 - 140*I2*I4 + 800*I6, 7*I2^2*I4 + 80*I4^2 - 30*I2*I6, -230*I2*I4^2 - 9*I2^2*I6 + 1040*I4*I6 + 108000*I10),
 (7*I2^2*I4 + 80*I4^2 - 30*I2*I6, 117*I2*I4^2 - 360*I4*I6 - 81000*I10, -50*I2^2*I4^2 + 20*I4^3 + 321*I2*I4*I6 - 540*I6^2 + 24300*I2*I10),
 (-230*I2*I4^2 - 9*I2^2*I6 + 1040*I4*I6 + 108000*I10, -50*I2^2*I4^2 + 20*I4^3 + 321*I2*I4*I6 - 540*I6^2 + 24300*I2*I10, -200*I2*I4^3 + 920*I4^2*I6 - 27*I2*I6^2 + 102600*I4*I10)])

# return the IC-simplified mestre cubic with indeterminates xis = [x1, x2, x3]
def ICmestrecubic(ICs, xis):
  (I2, I4, I6, I10) = ICs
  (x1, x2, x3) = xis
  a111 = (-1/90) * (27*I2^5 + 2000*I2^3*I4 - 41600*I2*I4^2 - 11400*I2^2*I6 + 192000*I4*I6 + 28800000*I10)
  a112 = (-1/30) * (-63*I2^4*I4 - 7780*I2^2*I4^2 + 270*I2^3*I6 - 3200*I4^3 + 67200*I2*I4*I6 - 144000*I6^2 + 1620000*I2*I10)
  a113 = (-1/10) * (-310*I2^3*I4^2 + 27*I2^4*I6 - 9200*I2*I4^3 + 3620*I2^2*I4*I6 + 44800*I4^2*I6 - 13200*I2*I6^2 + 162000*I2^2*I10 + 5280000*I4*I10)
  a122 = (-1/10) * (-I2^3*I4^2 - 620*I2*I4^3 + 330*I2^2*I4*I6 - 900*I2*I6^2 + 1080000*I4*I10)
  a123 = (1/15) * (225*I2^4*I4^2 + 8155*I2^2*I4^3 - 1161*I2^3*I4*I6 + 800*I4^4 - 75120*I2*I4^2*I6 + 1215*I2^2*I6^2 - 109350*I2^3*I10 + 165600*I4*I6^2 - 3969000*I2*I4*I10 + 19440000*I6*I10)
  a133 = (-1/30) * (-650*I2^3*I4^3 - 18700*I2*I4^4 + 270*I2^2*I4^2*I6 + 243*I2^3*I6^2 + 91200*I4^3*I6 + 33660*I2*I4*I6^2 + 340200*I2^2*I4*I10 - 129600*I6^3 + 10008000*I4^2*I10 + 1458000*I2*I6*I10)
  a222 = (9/10) * (53*I2^2*I4^3 + 40*I4^4 - 360*I2*I4^2*I6 + 600*I4*I6^2 - 30000*I2*I4*I10 + 90000*I6*I10)
  a223 = (-1/10) * (350*I2^3*I4^3 + 1540*I2*I4^4 - 3603*I2^2*I4^2*I6 - 6840*I4^3*I6 + 13140*I2*I4*I6^2 - 170100*I2^2*I4*I10 - 16200*I6^3 - 702000*I4^2*I10 + 729000*I2*I6*I10)
  a233 = (1/30) * (14650*I2^2*I4^4 + 1350*I2^3*I4^2*I6 + 200*I4^5 - 121920*I2*I4^3*I6 - 7533*I2^2*I4*I6^2 + 248760*I4^2*I6^2 + 9720*I2*I6^3 - 15163200*I2*I4^2*I10 - 656100*I2^2*I6*I10 + 63666000*I4*I6*I10 + 3936600000*I10^2)
  a333 = (-1/90) * (5000*I2^3*I4^4 - 9500*I2*I4^5 - 65850*I2^2*I4^3*I6 + 46200*I4^4*I6 + 297540*I2*I4^2*I6^2 + 729*I2^2*I6^3 - 4860000*I2^2*I4^2*I10 - 476280*I4*I6^3 + 4986000*I4^3*I10 + 32221800*I2*I4*I6*I10 - 43740000*I6^2*I10 + 1180980000*I2*I10^2)
  return a111*x1^3 + a112*x1^2*x2 + a113*x1^2*x3 + a122*x1*x2^2 + a123*x1*x2*x3 + a133*x1*x3^2 + a222*x2^3 + a223*x2^2*x3 + a233*x2*x3^2 + a333*x3^3
#  return a111*x1^3 + 3*a112*x1^2*x2 + 3*a113*x1^2*x3 + 3*a122*x1*x2^2 + 6*a123*x1*x2*x3 + 3*a133*x1*x3^2 + a222*x2^3 + 3*a223*x2^2*x3 + 3*a233*x2*x3^2 + a333*x3^3

# given ICs, use the IC-simplified Mestre conic and cubic to generate a
# genus 2 curve
# INPUT : list of rational ICs : [I2, I4, I6, I10]
# OUTPUT : 0 if Mestre conic is singular (reduced automorphism group is even)
#	 : -1 if Mestre conic has no rational point (curve not defined over Q)
#	 : f(x) s.t. y^2 = f(x) is a rational curve with given ICs

def IC2g2(ICs):
  R.<x> = QQ[]
  L = ICmestre(ICs)
  C = Conic(L)
  if C.is_singular():
    return 0 
  if not C.has_rational_point():
    return -1
  param = C.parametrization()[0]
  x1 = param[0](x,1)
  x2 = param[1](x,1)
  x3 = param[2](x,1)
  f = ICmestrecubic(ICs,(x1,x2,x3))
  return f
