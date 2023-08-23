import sys
sys.path.append('/home/edgarcosta/projects/LMFDB/lmfdb')
from lmfdb import db
# build DBs


forms = {elt['label'] : elt for elt in db.mf_newforms.search({'dim':2, 'weight':2,'char_order':1}, ['label','hecke_orbit_code'])}
all_hoc = [elt['hecke_orbit_code'] for elt  in forms.values()]
lpoly_dict = {(elt['hecke_orbit_code'], elt['p']) : tuple(elt['lpoly']) for elt in  db.mf_hecke_lpolys.search({'hecke_orbit_code': {'$in': all_hoc }}, ['p', 'lpoly', 'hecke_orbit_code'])} 
primes = sorted(list(set(elt[1] for elt in lpoly_dict)))

def convert(elt):
    return elt['has_jacobian'] == 1, elt['has_principal_polarization'] == 1, elt['is_geometrically_simple']
localfactorsdb = dict()
for p in primes: # we only have data up to 211
    localfactorsdb[p] = {tuple(elt['poly']) : convert(elt)
                for elt in db.av_fq_isog.search(
                    {'g':2, 'q': p},
                    ['poly', 'has_jacobian', 'has_principal_polarization', 'is_geometrically_simple'])}

def do_one_example(label):
    hoc = forms[label]['hecke_orbit_code']
    notlocalpp = []
    notlocaljacgeosimple = []
    notlocaljac = []
    for p in primes:
        lpoly = lpoly_dict[(hoc, p)]
        if len(lpoly) == 5:
            has_jacobian, has_pp, isgeomsimple = localfactorsdb[p][lpoly]
            if not has_jacobian:
                notlocaljac.append(p)
                if isgeomsimple: #Seeing if there might an obstruction to being a jacobian and is geometrically simple.`
                    notlocaljacgeosimple.append(p)
            if not has_pp:
                notlocalpp.append(p)

    return notlocalpp, notlocaljacgeosimple, notlocaljac

obstructed = dict()
for label in forms:
    obs = do_one_example(label)
    if any(obs):
        obstructed[label] = obs

with open("locally_obstructed.txt", "w") as W:
    W.write(":".join(["label", "no local PP", "no local Jacobian and is geometrically simple", "no local Jacobian"]) + '\n')
    output = [[label] + list(elt) for label, elt in obstructed.items()]
    output.sort(key=lambda elt: (-len(elt[1]), -len(elt[2]), -len(elt[3])))
    for elt in output:
        out = ":".join(map(str, elt))
        out = out.replace(' ', '')
        W.write(out + "\n")


