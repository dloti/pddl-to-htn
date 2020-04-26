import subprocess
import argparse
import os


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-i', '--input', help='input domain name')
    parser.add_argument('-o', '--output', help='output path for generated htns')
    args = parser.parse_args()

    out_path = os.path.normpath(args.output)
    spec_file_path = os.path.join("./domains",args.input,args.input+".spec")
    prob_list_path = os.path.normpath(args.output+'/prob_list.txt')

    with open(spec_file_path) as f:
        content = f.readlines()
        domain = content[0].rstrip()
        path = content[1].rstrip()
        domain_file = content[2].rstrip()
        rep_instance = content[3].rstrip()
        problems = content[4:]

    with open(os.path.join(out_path,domain),'w') as domain_out:
        domain_path = path+domain_file
        subprocess.call(["./bin/create_htn", domain, domain_path, path+rep_instance], stdout=domain_out)

    with open(prob_list_path,'w') as prob_list:
        for problem in problems:
            problem = problem.rstrip()
            problem_path = path+problem
            tmp = problem.rsplit('/')
            if len(tmp) > 1:
                problem = '-'.join(tmp)
            prob_list.write(problem.rstrip('.pddl')+'\n')
            if problem == '':
                continue
            problem_out = open(args.output+'/'+problem.rstrip('.pddl'),'w')
            subprocess.call(["./bin/initialize", domain, domain_path, problem_path], stdout=problem_out)
            problem_out.close()
    prob_list.close()

    #subprocess.call(["sbcl", '--script', 'script.txt','>','result.txt'])

if __name__ == "__main__":
    main()
