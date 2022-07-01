import sys
sys.path.append("./common")
from utils import read_instance

for i in range(1,41):

    tDim = []
    
    # W, n, rectangles
    w, t, tDim = read_instance("./instances/ins-%d.txt"%i)

    with open("./CP/CP_instances/ins-%d.dzn"%i, "w") as f:
        s = "w = "+str(w)+";\n"
        s = s + "n = "+str(t)+";\n"
        s = s + "dims = ["
        for i in range(t):
            s = s + "|"
            for j in range(len(tDim[i])):
                s=s+str(tDim[i][j])
                if j < len(tDim[i])-1:
                    s = s+", "
            if i<t-1:
                s= s+ ",\n"
            else:
                s= s + "|];"
        f.write(s)