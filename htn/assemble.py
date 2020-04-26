#!/usr/bin/python

import subprocess
import argparse


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-i', '--input', help='input domain')
    parser.add_argument('-p', '--path', help='output path')
    args = parser.parse_args()

    with open('domains/'+args.input+'/'+args.input+'.spec') as f:
        content = f.readlines()
        domain = content[0].rstrip()
        path = content[1].rstrip()
        domain_file = content[2].rstrip()
        rep_instance = content[3].rstrip()
        problems = content[4:]

    domain_out = open(args.path+'/'+domain,'w')
    domain_path = path+domain_file
    subprocess.call(["./bin/create_htn", domain, domain_path, path+rep_instance], stdout=domain_out)

    with open(args.path+'/prob_list.txt','w') as prob_list:
        for problem in problems:
            problem = problem.rstrip()
            problem_path = path+problem
            tmp = problem.rsplit('/')
            if len(tmp) > 1:
                problem = '-'.join(tmp)
            prob_list.write(problem.rstrip('.pddl')+'\n')
            if problem == '':
                continue
            problem_out = open(args.path+'/'+problem.rstrip('.pddl'),'w')
            subprocess.call(["./bin/initialize", domain, domain_path, problem_path], stdout=problem_out)
            problem_out.close()
    prob_list.close()

    #subprocess.call(["sbcl", '--script', 'script.txt','>','result.txt'])

if __name__ == "__main__":
    main()
