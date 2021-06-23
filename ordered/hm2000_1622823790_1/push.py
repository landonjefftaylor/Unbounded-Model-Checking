import os

for i in range(162282,162319):
  os.system("git add " + str(i) + "*")
  os.system("git commit -m 'found 6-22-21'")
  os.system("git push origin main")
  print("git pushed " + str(i) + "*")
  if i == 1:
    input("click enter")

