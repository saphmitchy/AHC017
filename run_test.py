import os
import joblib

n_parallel = 3
n_tests = 100

def get_score(seed: int) -> int:
    inputfile = f"tools/in/{seed:04}.txt"
    outputfile = f"tools/out/{seed:04}.txt"
    os.system(f"./main < {inputfile} > {outputfile}")
    out = os.popen(f"tools/target/release/vis {inputfile} {outputfile}")
    return int(out.read().split()[-1])

def run_all():
    res = joblib.Parallel(n_jobs=n_parallel, verbose=10)(joblib.delayed(get_score)(i) for i in range(n_tests))
    print(res)
    print(sum(res))

if __name__ == '__main__':
    os.system("g++ -std=gnu++17 -Wall -Wextra -O2  main.cpp -o main")
    run_all()