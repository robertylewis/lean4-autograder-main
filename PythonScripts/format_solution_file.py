import re 
import collections

COMMENT_PATTERN = "^/-.*-/$"
PROBLEM_PATTERN = "^(theorem|lemma){1}.*"

PROBLEMS = re.compile(PROBLEM_PATTERN)
COMMENTS = re.compile(COMMENT_PATTERN)

def locates_theorem_and_adds_sorry(queue, file):
    while len(queue) > 0:
        line = queue.popleft()
        pos = line.find(':=')
        if pos != -1:
            file.append(line[: pos + 2] + " sorry")
            return
        else: 
            file.append(line)
            file.append('\n')

def replaces_theorem_solution_by_sorrys(queue):
    file = []
    should_ignore = False
    while len(queue) > 0:
        line = queue.popleft()
        if PROBLEMS.match(line.strip()):
            queue.appendleft(line)
            locates_theorem_and_adds_sorry(queue, file)
            should_ignore = True
            file.append('\n\n')
        elif COMMENTS.match(line.strip()) and len(queue) > 0 and PROBLEMS.match(queue[0]):
            should_ignore = False
        
        if not should_ignore:
            file.append(line)
            file.append('\n')
    
    return file

# replaces theorem solutions by sorry's
def creates_template_from_solution(text) -> str: 
    queue = collections.deque(text)
    new_file = replaces_theorem_solution_by_sorrys(queue)

    return ''.join(new_file)
