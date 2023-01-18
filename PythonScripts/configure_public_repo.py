import json
import github as github
from datetime import date
from format_solution_file import creates_template_from_solution

# reads config from file
f = open('../api_config.json')
api_config = json.load(f)

f = open('../autograder_config.json')
autograder_config = json.load(f)

# gets pointer to private repo
git = github.Github(api_config['api_key'])
private_repo = git.get_repo(autograder_config['private_repo'])
user = git.get_user()

commit_message = "Assignment files - " + date.today().strftime("%m/%d/%y")

try:
    # tries to create new public repo 
    new_repo = user.create_repo(autograder_config['public_repo'].split('/')[1])

    # adds all project files to public repo (except the assignments)
    contents = private_repo.get_contents("")
    for content_file in contents:
        if content_file.type != "dir":
            new_repo.create_file(content_file.path, commit_message, content_file.decoded_content.decode("utf-8"))

except github.GithubException:
    print ("Repo already exists, commiting a new file instead") 

    # if public repo already exists, gets a pointer to it
    new_repo = git.get_repo(autograder_config['public_repo'])

# gets assignment file
content = private_repo.get_contents(autograder_config['assignment_path'])
text = content.decoded_content.decode("utf-8").split('\n')

# creates template
assignment_file = creates_template_from_solution(text)

# adds template to public repo
new_repo.create_file(autograder_config['assignment_path'], commit_message, assignment_file)
