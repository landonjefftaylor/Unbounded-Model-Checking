import os
import time
import random

#Did the ivy_check action return an error?
def check_failed(file_name):
  with open(file_name, 'r') as read_obj:
    for line in read_obj:
      if "error:" in line:
        print("IVY RETURNED ERROR")
        return True
      if "not found: " in line:
        print("IVY RETURNED NOT FOUND")
        return True
  return False

#Did the ivy_check action return a passing trace?
def check_pass(file_name):
  with open(file_name, 'r') as read_obj:
    for line in read_obj:
      if "PASS" in line:
        return True
  return False

class Node:
  #Create a node:
  def __init__(self, data):
    self.children = []
    self.data = data
  
  #Add a child to a node:
  def add_kid(self, newNode):
    self.children.append(newNode)
  
  #Print the tree in an indented list:
  def print_tree(self, level, newline):
    returnstring = str(self.data) 
    if self.data == "":
      returnstring = ""
      for child in self.children:
        returnstring = returnstring + child.print_tree(0, True)
      return returnstring
    if newline:
      for i in range(0,level):
        returnstring = "> " + returnstring
      returnstring = "\n" + returnstring
    else:
      returnstring = " > " + returnstring
    if (len(self.children) == 1):
      returnstring = returnstring + self.children[0].print_tree(level, False) 
    else:
      for child in self.children:
        returnstring = returnstring + child.print_tree(level + 1, True)
    return returnstring

#Welcome and initialization
print("LET'S MAKE SOME CONES! Your folder options are:")
path = '.'
directory_contents = os.listdir(path)
for item in directory_contents:
  if os.path.isdir(item):
    print(item)
print("")

foldername = input("Input the name of the folder: ")

#Initialize the backward folder elements
print("Now dealing with cones. This may take a few minutes.")
root = Node("")
finished = False
index = 0
log = open(foldername + "/log.txt")

#Use the lines from the log (created earlier) to get more paths
for logline in log: 
  
  #Housekeeping
  tracefile = foldername + "/" + str(index) + ".txt"
  if check_failed(tracefile):
    print("\033[0;30;41mFAILURE: IVY ERROR!!! Big oops.\033[0m")
    exit()
  elif check_pass(tracefile):
    print("Finishd item " + str(index - 1) + ".")
    if index == 0:
      print("\033[0;30;42mNOTHING FOUND!\033[0m")
    break
  
  #Set up folders and files
  bfolder = foldername + "/" + str(index)

  #Housekeeping
  subindex = 0
  finished = False

  #Find all the backward-steps up to k away
  while True:
    
    #Check in IVy
    tracefile = bfolder + "/" + str(subindex) + "_abr.txt"
    if not(os.path.isfile(tracefile)):
      # finished = True
      break
    #Check for errors or passing 
    elif check_failed(tracefile):
      print("\033[0;30;41mFAILURE: IVY ERROR!!! Big oops.\033[0m")
      exit()
    elif check_pass(tracefile):
      print("Testing has completed.")
      if subindex == 0:
        print("\033[0;30;42mNOTHING FOUND 2!\033[0m")
      # finished = True
      break

    #Add to the cone
    with open(tracefile) as abr:
      currstate = root
      for abrline in abr:
        newkid = True
        for child in currstate.children:
          if abrline.rstrip("\n") in child.data:
            currstate = child
            newkid = False
            break
        if newkid:
          currstate.add_kid(Node(abrline.rstrip("\n")))
          currstate = currstate.children[len(currstate.children) - 1]

    subindex = subindex + 1

  index = index + 1
log.close()

#Write the cone and wrap up
with open(foldername + "/conefile.txt", 'w') as conefile:
  conefile.write(root.print_tree(0, True))

print("FINISHED!")
print("\n\n###################################################################################")
print("###################################################################################")
print("###################################################################################\n\n")
