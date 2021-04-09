import os
import time

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

def check_pass(file_name):
  with open(file_name, 'r') as read_obj:
    for line in read_obj:
      if "PASS" in line:
        return True
  return False

print("GETCASES PLUS BACKWARD REACHABILITY - WOOHOO!! Your file options are:")
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
foldername = str(totest) + "_" + ts + "_" + str(upperbound)

os.system("mkdir " + foldername)

logfile = open(foldername + "/log.txt", 'a')

with open(totest + ".ivy", 'r') as old:
  with open(foldername + "/0.ivy", 'w') as new:
    for line in old:
      new.write(line)

print("All files opened correctly. Expect a large number of beeps once the script is finished.")
print("Look in this folder once completed: " + foldername)

index = 0
finished = False

while not(finished): # and index < 200:

  timer_start = time.time()
  new_invariant = ""
  tracefile = foldername + "/" + str(index) + ".txt"
  os.system("ivy_check trace=true " + foldername + "/" + str(index) + ".ivy > " + tracefile)

  if check_failed(tracefile):
    print("\033[0;30;41mFAILURE: IVY ERROR!!! Big oops.\033[0m")
    exit()

  elif check_pass(tracefile):
    print("Testing has completed.")
    if index == 0:
      print("\033[0;30;42mNO PROGRESS MADE!\033[0m")
    finished = True
    break

  endtrace = False
  tetr = 0
  laci = 0
  trash = ""

  with open(tracefile) as trace:
    for line in trace:
      if "   tetr_def.tetr = " in line:
        s = line.split(" = ")
        clean = s[1].rstrip('\n')
        if clean.isdigit():
          tetr = str(clean)
        else:
          print("TETR WAS NOT A DIGIT. GOT _" + clean + "_")
      elif "   laci_def.laci = " in line:
        s = line.split(" = ")
        clean = s[1].rstrip('\n')
        if clean.isdigit():
          laci = str(clean)
        else:
          print("LACI WAS NOT A DIGIT. GOT _" + clean + "_")

  new_invariant = " | (tetr_def.tetr = " + str(tetr) + " & laci_def.laci = " + str(laci) + ")"
  with open(foldername + "/" + str(index) + ".ivy", 'r') as old:
    with open(foldername + "/" + str(index + 1) +".ivy", 'w') as new:
      for line in old:
        if "invariant" in line:
          break
        else:
          new.write(line)
      if new_invariant in line:
        print("Woah there, cowboy. The following is already in this line:\n" + new_invariant)
      new.write(line.rstrip('\n') + new_invariant)
      logfile.write("tetr " + str(tetr) + " laci " + str(laci) + "\n")

  timer_duration = time.time() - timer_start
  print("Checked index " + str(index), end="")
  print(" in %.2f seconds" % timer_duration)
  index = index + 1

logfile.close()

# DEALING WITH BACKWARD REACHABILITY

print("Now dealing with backward reachability. This may take some time.")


finished = False
index = 0
log = open(foldername + "/log.txt")
for logline in log: #eventually incorporate the upper bound
  tracefile = foldername + "/" + str(index) + ".txt"
  if check_failed(tracefile):
    print("\033[0;30;41mFAILURE: IVY ERROR!!! Big oops.\033[0m")
    exit()
  elif check_pass(tracefile):
    print("Testing has completed.")
    if index == 0:
      print("\033[0;30;42mNOTHING FOUND!\033[0m")
    break
  bfolder = foldername + "/" + str(index)
  os.system("mkdir " + bfolder)
  logdata = logline.split(" ")
  logassume = "    assume ~(laci_def.laci >= 20 | tetr_def.tetr <= 40) -> (laci_def.laci = " + logdata[3].rstrip("\n") + " & tetr_def.tetr = " + logdata[1].rstrip("\n") + ");"
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
            new.write("    t" + str(i) + " := t" + str(i-1) + ";\n")
            new.write("    l" + str(i) + " := l" + str(i-1) + ";\n")
          new.write("    t0 := tetr_def.tetr;\n")
          new.write("    l0 := laci_def.laci;\n\n")
        elif "var rand : bool" in line:
          new.write("var rand : bool\n")
          for i in range(0, upperbound):
            new.write("var t" + str(i) + " : bv8\nvar l" + str(i) + ": bv8\n")
        else:
          new.write(line)
      new.write("invariant (laci_def.laci >= 20 | tetr_def.tetr <= 40)")
  # os.system("ivy_check trace=true " + bfolder + "/0.ivy > " + bfolder + "/0.txt")
  subindex = 0
  finished = False
  newlog = open(bfolder + "/log.txt", 'w')
  newlog.write("Testing endpoint tetr=" + logdata[1].rstrip("\n") + " and laci=" + logdata[3].rstrip("\n") + "\n")
  while not(finished):
    os.system("ivy_check trace=true " + bfolder + "/" + str(subindex) + ".ivy > " + bfolder + "/" + str(subindex) + ".txt")
    print("Checked item " + str(index) + "." + str(subindex))
    tracefile = bfolder + "/" + str(subindex) + ".txt"
    if check_failed(tracefile):
      print("\033[0;30;41mFAILURE: IVY ERROR!!! Big oops.\033[0m")
      exit()
    elif check_pass(tracefile):
      print("Testing has completed.")
      if subindex == 0:
        print("\033[0;30;42mNOTHING FOUND 2!\033[0m")
      finished = True
      break
    t = [0] * upperbound 
    l = [0] * upperbound 
    with open(tracefile) as trace:
      for line in trace:
        for i in range(0,upperbound):
          if ("  t" + str(i) + " = ") in line:
            s = line.split(" = ")
            clean = s[1].rstrip('\n')
            if clean.isdigit():
              t[i] = str(clean)
          elif ("  l" + str(i) + " = ") in line:
            s = line.split(" = ")
            clean = s[1].rstrip('\n')
            if clean.isdigit():
              l[i] = str(clean)
    with open(bfolder + "/" + str(subindex) + ".ivy", 'r') as old:
      with open(bfolder + "/" + str(subindex + 1) + ".ivy", 'w') as new:
        for line in old:
          if "invariant " in line:
            break
          else:
            new.write(line)
        new.write(line.rstrip('\n') + " | (")
        for i in range(0,upperbound):
          new.write("t" + str(i) + " = " + str(t[i]) + " & l" + str(i) + " = " + str(l[i]) )
          newlog.write("t" + str(i) + " = " + str(t[i]) + " ; l" + str(i) + " = " + str(l[i]))
          if (i < upperbound - 1):
            new.write(" & ")
            newlog.write(" <- ")
        new.write(")")
        newlog.write("\n")
    subindex = subindex + 1
  newlog.close()
  index = index + 1
logfile.close()

print("FINISHED!")
print("\n\n###################################################################################")
print("###################################################################################")
print("###################################################################################\n\n")
