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
    elif (len(self.children) == 0):
      returnstring = returnstring + "==FINAL==" 
    else:
      for child in self.children:
        returnstring = returnstring + child.print_tree(level + 1, True)
    return returnstring


################################################################################
# DEALING WITH BACKWARD REACHABILITY ###########################################
################################################################################

def backward_reach(starting_index, foldername):
  #Initialize the backward folder elements
  print("Dealing with backward reachability. Starting index " + str(starting_index))
  finished = False
  index = starting_index
  log = open(foldername + "/log.txt")

  for i in range(0,starting_index):
    next(log)

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
    os.system("mkdir " + bfolder)
    logdata = logline.split(" ")
    # Log in format "amtr " + amtr + " beti " + beti + " hlyiir" + hlyiir + " phlf " + phlf + " yfp " + yfp +
    logassume = "    assume ~(yfp.protein < 30) -> (amtr.protein = " + logdata[1].rstrip("\n") + " & beti.protein = " + logdata[3].rstrip("\n") + " & hlyiir.protein = " + logdata[5].rstrip("\n") + " & phlf.protein = " + logdata[7].rstrip("\n") + " & yfp.protein = " + logdata[9].rstrip("\n") + ");"

    #Copy the file over
    with open(foldername + "/" + str(index) + ".ivy", 'r') as old:
      with open(bfolder + "/0.ivy", 'w') as new:
        for line in old:
          if "invariant " in line:
            break
          elif "#Add assumption here" in line:
            new.write(logassume)
          elif "action administrate" in line:
            new.write("  action administrate = {\n\n")
            for i in range(upperbound - 1, 0, -1):
              new.write("    a" + str(i) + " := a" + str(i-1) + ";\n")
              new.write("    b" + str(i) + " := b" + str(i-1) + ";\n")
              new.write("    h" + str(i) + " := h" + str(i-1) + ";\n")
              new.write("    p" + str(i) + " := p" + str(i-1) + ";\n")
              new.write("    y" + str(i) + " := y" + str(i-1) + ";\n")
            new.write("    a0 := amtr.protein;\n")
            new.write("    b0 := beti.protein;\n")
            new.write("    h0 := hlyiir.protein;\n")
            new.write("    p0 := phlf.protein;\n")
            new.write("    y0 := yfp.protein;\n\n")
          elif "var max : bv8" in line:
            new.write("var max : bv8\n\n")
            for i in range(0, upperbound):
              new.write("var a" + str(i) + " : bv8\nvar b" + str(i) + ": bv8\nvar h" + str(i) + " : bv8\nvar p" + str(i) + " : bv8\nvar y" + str(i) + " : bv8\n")
          else:
            new.write(line)
        new.write("invariant yfp.protein < 30")
    
    #Housekeeping
    subindex = 0
    finished = False
    newlog = open(bfolder + "/log.txt", 'w')
    newlog.write("Testing endpoint amtr=" + logdata[1].rstrip("\n") + " beti=" + logdata[3].rstrip("\n") + " hlyiir=" + logdata[5].rstrip("\n") + " phlf=" + logdata[7].rstrip("\n") + " yfp=" + logdata[9].rstrip("\n") + "\n")

    #Find all the backward-steps up to k away
    while not(finished):
      
      #Check in IVy
      tracefile = bfolder + "/" + str(subindex) + ".txt"
      os.system("ivy_check trace=true " + bfolder + "/" + str(subindex) + ".ivy > " + tracefile)
      print("Checked item " + str(index) + "." + str(subindex))
      
      #Check for errors or passing 
      if check_failed(tracefile):
        print("\033[0;30;41mFAILURE: IVY ERROR!!! Big oops.\033[0m")
        exit()
      elif check_pass(tracefile):
        print("This phase of backward reachability has completed.")
        if subindex == 0:
          print("\033[0;30;42mNOTHING FOUND 2!\033[0m")
        finished = True
        break
      
      #Get all the information out of the trace file
      abr_a = '999'
      abr_b = '999'
      abr_h = '999'
      abr_p = '999'
      abr_y = '999'
      lastaction = "initial_state"

      abrfile = bfolder + "/" + str(subindex) + "_abr.txt"
      a = [0] * upperbound 
      b = [0] * upperbound 
      h = [0] * upperbound 
      p = [0] * upperbound 
      y = [0] * upperbound 
      
      with open(tracefile) as trace:
        with open(abrfile, 'w') as abr:
          for line in trace:
            for i in range(0,upperbound):
              if ("  a" + str(i) + " = ") in line:
                s = line.split(" = ")
                clean = s[1].rstrip('\n')
                if clean.isdigit():
                  a[i] = str(clean)
              elif ("  b" + str(i) + " = ") in line:
                s = line.split(" = ")
                clean = s[1].rstrip('\n')
                if clean.isdigit():
                  b[i] = str(clean)
              elif ("  h" + str(i) + " = ") in line:
                s = line.split(" = ")
                clean = s[1].rstrip('\n')
                if clean.isdigit():
                  h[i] = str(clean)
              elif ("  p" + str(i) + " = ") in line:
                s = line.split(" = ")
                clean = s[1].rstrip('\n')
                if clean.isdigit():
                  p[i] = str(clean)
              elif ("  y" + str(i) + " = ") in line:
                s = line.split(" = ")
                clean = s[1].rstrip('\n')
                if clean.isdigit():
                  y[i] = str(clean)
            if ("call " in line):
              lastaction = line.split("call ")[1].rstrip("\n")
            if ("    amtr.protein = ") in line:
              s = line.split(" = ")
              clean = s[1].rstrip('\n')
              if clean.isdigit():
                abr_a = str(clean)
                if not(abr_a == '999' or abr_b == '999' or abr_h == '999' or abr_p == '999' or abr_y == '999'):
                  abr.write("a " + abr_a + " b " + abr_b + " h " + abr_h + " p " + abr_p + " y " + abr_y + " _" + lastaction + "_\n")
            elif ("    beti.protein = ") in line:
              s = line.split(" = ")
              clean = s[1].rstrip('\n')
              if clean.isdigit():
                abr_b = str(clean)
                if not(abr_a == '999' or abr_b == '999' or abr_h == '999' or abr_p == '999' or abr_y == '999'):
                  abr.write("a " + abr_a + " b " + abr_b + " h " + abr_h + " p " + abr_p + " y " + abr_y + " _" + lastaction + "_\n")
            elif ("    hlyiir.protein = ") in line:
              s = line.split(" = ")
              clean = s[1].rstrip('\n')
              if clean.isdigit():
                abr_h = str(clean)
                if not(abr_a == '999' or abr_b == '999' or abr_h == '999' or abr_p == '999' or abr_y == '999'):
                  abr.write("a " + abr_a + " b " + abr_b + " h " + abr_h + " p " + abr_p + " y " + abr_y + " _" + lastaction + "_\n")
            elif ("    phlf.protein = ") in line:
              s = line.split(" = ")
              clean = s[1].rstrip('\n')
              if clean.isdigit():
                abr_p = str(clean)
                if not(abr_a == '999' or abr_b == '999' or abr_h == '999' or abr_p == '999' or abr_y == '999'):
                  abr.write("a " + abr_a + " b " + abr_b + " h " + abr_h + " p " + abr_p + " y " + abr_y + " _" + lastaction + "_\n")
            elif ("    yfp.protein = ") in line:
              s = line.split(" = ")
              clean = s[1].rstrip('\n')
              if clean.isdigit():
                abr_y = str(clean)
                if not(abr_a == '999' or abr_b == '999' or abr_h == '999' or abr_p == '999' or abr_y == '999'):
                  abr.write("a " + abr_a + " b " + abr_b + " h " + abr_h + " p " + abr_p + " y " + abr_y + " _" + lastaction + "_\n")
      
      #Move on to the next file
      with open(bfolder + "/" + str(subindex) + ".ivy", 'r') as old:
        with open(bfolder + "/" + str(subindex + 1) + ".ivy", 'w') as new:
          for line in old:
            if "invariant " in line:
              break
            else:
              new.write(line)
          new.write(line.rstrip('\n') + " | (")
          for i in range(0,upperbound):
            new.write("a" + str(i) + " = " + str(a[i]) + " & b" + str(i) + " = " + str(b[i]) + " & h" + str(i) + " = " + str(h[i]) + " & p" + str(i) + " = " + str(p[i]) + " & y" + str(i) + " = " + str(y[i]) )
            newlog.write("a" + str(i) + " = " + str(a[i]) + " & b" + str(i) + " = " + str(b[i]) + " & h" + str(i) + " = " + str(h[i]) + " & p" + str(i) + " = " + str(p[i]) + " & y" + str(i) + " = " + str(y[i]) + "\n" )
            if (i < upperbound - 1):
              new.write(" & ")
              newlog.write(" <- ")
          new.write(")")
          newlog.write("\n")
      subindex = subindex + 1
    newlog.close()
    index = index + 1
  # logfile.close()


#Welcome and initialization
print("Your file options are:")
os.system("ls *.ivy")
print("")

totest = input("Input the name of the file without using .ivy: ")
while totest.endswith == ".ivy":
  totest = input("YOU HAD ONE JOB! Try again without using .ivy: ")
ts = str(int(time.time()))

upperboundstr = input("How many steps back would you like to take? ")
while not(upperboundstr.isdigit()):
  upperboundstr = input("ENTER A DIGIT!\nHow many steps back would you like to take? ")
upperbound = int(upperboundstr)

indexlimitstr = input("You can limit the number of traces you get back.\nEnter a number or 'n': ")
if not(indexlimitstr.isdigit()):
  indexlimit = 9999999999999
else:
  indexlimit = int(indexlimitstr)

intervalstr = input("Do backward reachability after __ traces: ")
if not(intervalstr.isdigit()):
  interval = 20
else:
  interval = int(intervalstr)


#Open the working directory
foldername = str(totest) + "_" + ts + "_" + str(upperbound) 
os.system("mkdir " + foldername)
logfile = open(foldername + "/log.txt", 'a')

#Copy the file to test into the working directory
#This prevents the file from being modified in error
with open(totest + ".ivy", 'r') as old:
  with open(foldername + "/0.ivy", 'w') as new:
    for line in old:
      new.write(line)

print("All files opened correctly.")
print("Look in this folder once completed: " + foldername)
print("-----------")

index = 0
last_backward_index = 0
finished = False

#Find all the possible "bad states"
while not(finished) and index < indexlimit:

  if (index % interval == 0 and index > 0):
    logfile.close()
    last_backward_index = index - interval
    backward_reach(last_backward_index, foldername)
    logfile = open(foldername + "/log.txt", 'a')

  #Initialize
  timer_start = time.time()
  new_invariant = ""
  tracefile = foldername + "/" + str(index) + ".txt"
  
  #Check the model
  os.system("ivy_check trace=true " + foldername + "/" + str(index) + ".ivy > " + tracefile)
  
  #Check for errors or passing states
  if check_failed(tracefile):
    print("\033[0;30;41mFAILURE: IVY ERROR!!! Big oops.\033[0m")
    exit()
  elif check_pass(tracefile):
    print("Finding bad states has completed.")
    if index == 0:
      print("\033[0;30;42mNO PROGRESS MADE!\033[0m")
    finished = True
    break

  endtrace = False
  amtr   = "NOT DEFINED error"
  beti   = "NOT DEFINED error"
  hlyiir = "NOT DEFINED error"
  phlf   = "NOT DEFINED error"
  yfp    = "NOT DEFINED error"

  #Examine the trace to find bad state
  with open(tracefile) as trace:
    for line in trace:
      if "   amtr.protein = " in line:
        s = line.split(" = ")
        clean = s[1].rstrip('\n')
        if clean.isdigit():
          amtr = str(clean)
        else:
          print("AMTR WAS NOT A DIGIT. GOT _" + clean + "_")
      elif "   beti.protein = " in line:
        s = line.split(" = ")
        clean = s[1].rstrip('\n')
        if clean.isdigit():
          beti = str(clean)
        else:
          print("BETI WAS NOT A DIGIT. GOT _" + clean + "_")
      elif "   hlyiir.protein = " in line:
        s = line.split(" = ")
        clean = s[1].rstrip('\n')
        if clean.isdigit():
          hlyiir = str(clean)
        else:
          print("HLYIIR WAS NOT A DIGIT. GOT _" + clean + "_")
      elif "   phlf.protein = " in line:
        s = line.split(" = ")
        clean = s[1].rstrip('\n')
        if clean.isdigit():
          phlf = str(clean)
        else:
          print("PHLF WAS NOT A DIGIT. GOT _" + clean + "_")
      elif "   yfp.protein = " in line:
        s = line.split(" = ")
        clean = s[1].rstrip('\n')
        if clean.isdigit():
          yfp = str(clean)
        else:
          print("YFP WAS NOT A DIGIT. GOT _" + clean + "_")
  
  #Use that information to add to the invariant
  new_invariant = " | (amtr.protein = " + amtr + " & beti.protein = " + beti + " & hlyiir.protein = " + hlyiir + " & phlf.protein = " + phlf + " & yfp.protein = " + yfp + ")"

  #Add the invariant to the next file
  with open(foldername + "/" + str(index) + ".ivy", 'r') as old:
    with open(foldername + "/" + str(index + 1) +".ivy", 'w') as new:
      for line in old:
        if "invariant" in line:
          break
        else:
          new.write(line)
      if new_invariant in line:
        print("Woah there, cowboy. The following is already in this line:\n" + new_invariant)
        logfile.write("Woah there, cowboy. The following is already in this line: " + new_invariant + "\n")
      new.write(line.rstrip('\n') + new_invariant)
      logfile.write("amtr " + amtr + " beti " + beti + " hlyiir " + hlyiir + " phlf " + phlf + " yfp " + yfp + "\n")

  #Wrap things up
  timer_duration = time.time() - timer_start
  print("Checked index " + str(index), end="")
  print(" in %.2f seconds" % timer_duration)
  index = index + 1

logfile.close()
backward_reach(last_backward_index, foldername)


root = Node("")
logfile = open(foldername + "/log.txt", 'r')

index = 0
for line in logfile:
  subindex = 0
  while os.path.exists(foldername + "/" + str(index) + "/" + str(subindex) + "_abr.txt"):
    abrfile = foldername + "/" + str(index) + "/" + str(subindex) + "_abr.txt"
    with open(abrfile) as abr:
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

#Write the cone and wrap up
with open(foldername + "/conefile.txt", 'a') as conefile:
  conefile.write(root.print_tree(0, True))


logfile.close()

os.system("mv logfiles aigerfiles " + foldername + "/")

print("FINISHED!")
print("\n\n###################################################################################")
print("###################################################################################")
print("###################################################################################\n\n")
