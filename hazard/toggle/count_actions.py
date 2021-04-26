import os
import sys
from os import path

subdirectories = ""

if len(sys.argv) == 1:
  subdirectories = input("Check subfolders? y/n ")
else:
  subdirectories = sys.argv[1]

print("I'ma start counting actions in this folder.")

index = 0
finished = False
count_actions = []

while not(finished):
  print("Reading index " + str(index))
  if not(path.isfile(str(index) + ".txt")):
    finished = True
    break
  if not(os.access(str(index) + ".txt", os.R_OK)):
    finished = True
    break
  with open(str(index) + ".txt", 'r') as infile:
    action_count = 0
    for line in infile:
      if "call" in line:
        action_count = action_count + 1
    count_actions.append(action_count)
    index = index + 1

with open("report.txt",'w') as report:
  badness = 0
  badness_index = 0
  badness_list = []
  for i in range (0,index):
    working_index = count_actions.index(min(count_actions))
    if count_actions[working_index] == 0:
      print(" -- Ignored index " + str(working_index) + " due to zero steps or passing state -- " )
    else:
      badness_here = abs(badness_index - working_index)
      badness_list.append(badness_here)
      badness = badness + badness_here
      report.write(str(count_actions[working_index]).rjust(4) + " steps in test " + str(working_index).rjust(4) + " (badness " + str(badness_here).rjust(4) + " )\n")
      badness_index = badness_index + 1
    count_actions[working_index] = sys.maxsize
  report.write("\n\nBadness total:   " + str(badness).rjust(8))
  report.write("\nBadness average: " + str(int(sum(badness_list) / len(badness_list))).rjust(8))

print("Complete! Check report.txt in the folder [" + os.getcwd() + "].")

if 'y' in subdirectories:
  print("Now checking subdirectories.")
  index = 0
  while True:
    if path.isfile(str(index) + "/0.txt"):
      os.chdir(str(index))
      os.system("python3 ../../count_actions.py n") #the n means no subdir check
      os.chdir("../")
      index = index + 1
    else:
      break
  print("done with subdirectories.")