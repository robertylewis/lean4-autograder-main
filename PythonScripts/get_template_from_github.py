import json
import re
import os

COMMENT_PATTERN = "^/-.*-/$"
PROBLEM_PATTERN = "^(theorem|lemma){1}.*"

PROBLEMS = re.compile(PROBLEM_PATTERN)
COMMENTS = re.compile(COMMENT_PATTERN)

TEMPLATE_FILE = "../AutograderTests/Solution.lean"
EXERCISES_FILE = "../AutograderTests/exercises.txt"

def extract_exercises_names_and_points_from_template():
    names_and_points = {}
    points = 0
    comment = False
    with open(TEMPLATE_FILE, "r") as file:
        for line in file.readlines():
            line = line.strip()
            if COMMENTS.match(line):
                comment = True
                words = line.split(" ")
                points = words[1]
            else:
                if comment and PROBLEMS.match(line): 
                    words = line.split(" ")
                    names_and_points[words[1]] = int(points)
                comment = False
    return names_and_points

def write_exercises_file(names_and_points):
    file = open(EXERCISES_FILE, "w", encoding='utf8')
    for name, points in names_and_points.items():
        file.write(name + ';' + str(points) + '\n')
    file.close()

def main():
    # reads config from file
    f = open('../autograder_config.json')
    config = json.load(f)

    # removes old files if needed
    if os.path.exists(TEMPLATE_FILE):
        os.remove(TEMPLATE_FILE)
    if os.path.exists(EXERCISES_FILE):
        os.remove(EXERCISES_FILE)

    repo_name = config['public_repo'].split('/')[1]

    # downloads current assignment
    os.system("git clone https://github.com/" + config['public_repo'])
    os.system("mv " + repo_name + "/" + config['assignment_path'] + " " + TEMPLATE_FILE)
    os.system("rm -rf " + repo_name)

    # creates helper file
    names_and_points = extract_exercises_names_and_points_from_template()

    if len(names_and_points) == 0:
        print("Template file is not annotated with points.")

    write_exercises_file(names_and_points)

# starts script
main()
