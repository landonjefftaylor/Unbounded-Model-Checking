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

print("Let's go. Your file options are:")
os.system("ls *.ivy")
print("")

totest = input("Input the name of the file without using .ivy: ")
while totest.endswith == ".ivy":
  totest = input("YOU HAD ONE JOB! Try again without using .ivy: ")
ts = str(int(time.time()))
foldername = str(totest) + "_" + ts

os.system("mkdir " + foldername)

logfile = open(foldername + "/log.txt", 'a')

with open(totest + ".ivy", 'r') as old:
  with open(foldername + "/0.ivy", 'w') as new:
    for line in old:
      if "invariant (~flit.dropped)" in line:
        break
      else:
        new.write(line)

print("All files opened correctly. Expect a large number of beeps once the script is finished.")
print("Look in this folder once completed: " + foldername)

index = 0
finished = False

while not(finished): # and index < 200:

  timer_start = time.time()
  new_invariant = ""
  os.system("ivy_check trace=true " + foldername + "/" + str(index) + ".ivy > " + foldername + "/" + str(index) + ".txt")
  tracefile = foldername + "/" + str(index) + ".txt"

  if check_failed(tracefile):
    print("\033[0;30;41mFAILURE: IVY ERROR!!! Big oops.\033[0m")
    exit()

  elif check_pass(tracefile):
    print("Testing has completed.")
    if index == 0:
      print("\033[0;30;42mNO LIVELOCKS OR DROPS FOUND! HIP HIP HOORAY!\033[0m")
    finished = True
    break

  endtrace = False
  tetr = 0
  laci = 0
  trash = ""

  with open(tracefile) as trace:
    for line in trace:
      if "tetr_def.tetr = " in line:
        s = line.split(" = ")
        clean = s[1].rstrip('\n')
        if clean.isdigit():
          tetr = str(clean)
        else:
          print("TETR WAS NOT A DIGIT. GOT _" + clean + "_")
      elif "laci_def.laci = " in line:
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
      logfile.write("Added " + new_invariant + "\n")

  timer_duration = time.time() - timer_start
  print("Checked index " + str(index), end="")
  print(" in %.2f seconds" % timer_duration)
  index = index + 1

print("FINISHED!")
print("\n\n###################################################################################")
for x in range(0, 30):
	print("\a###################################################################################")
	time.sleep(0.1)
print("\n\n")
logfile.close()