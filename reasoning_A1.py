#!/usr/bin/env python
# coding: utf-8

# In[210]:


# fuction 1
def fun1(oprl,oprr):
    return '~' + oprl + '|' + oprr
def eliminate_implication(clause):
    i = 0
    while i < len(clause):
        if clause[i:i + 2] == '->':
          #  print(clause[i], i)
            l, r = i - 1, i + 2
            # sum pracket
            sum1 = 0
            bol = False
            if clause[l] == ')':
                bol = True
                l -= 1
                sum1 += 1
    #--------------------------------
            # this case handle []
            else :
                while clause[l] != '(':
                    l-=1
                l+=1
    #------------------------------
            while bol:
                if clause[l] == ')':
                    sum1 += 1
                elif clause[l] == '(':
                    sum1 -= 1
                if sum1 == 0:
                    break
                l -= 1
            strl = clause[l:i]

            bol = False
            if clause[r] == '(':
                bol = True
                r += 1
                sum1 += 1
              # print(sum1)
            while bol:
              # print(f" r = {r} len clause {len(clause)} and {clause[r]} and sum = {sum1}")
                if clause[r] == ')':
                    sum1 -= 1
                elif clause[r] == '(':
                    sum1 += 1
                if sum1 == 0:
                    break
                r += 1
            strr = clause[i + 2:r + 1]
            clause = clause[:l] + fun1(strl, strr) + clause[r + 1:]
        #   print(i+1, clause)
        i+=1
    return clause
    
    




        
                
                
            
            


# In[211]:


statment = "∃[𝑥]∀[𝑦]∀[𝑧] ((𝑃[𝑦] -> 𝑄[𝑧]) -> (𝑃[𝑥] -> 𝑄[𝑥]))"
print (f"statment = {statment} after apply eliminate_implication =\n {eliminate_implication(statment.replace(' ',''))}  ")
statment = eliminate_implication(statment.replace(" ",""))
print (statment)


# In[212]:


# fuction 2 , 3
def apply_negation(clause):
    i = len(clause) - 1 
    while i > 0:
       # print(i)
        sums = 0
        if clause[i-1:i+1] == '~(': 
            sums+=1
            j=i+1
            #clause[i-1] = ' '
            clause = clause[:i-1] + ' ' + clause[i:]
            while sums != 0:
                if clause[j] == '|':
                    #clause[j] = '&'
                    clause = clause[:j] + '&' + clause[j+1:]             
                elif clause[j] == '&':
                   # clause[j] = '|'
                    clause = clause[:j] + '|' + clause[j+1:]
                elif clause[j] == '∃':
                    #clause[j] = '∀'
                    clause = clause[:j] + '∀' + clause[j+1:]
                elif clause[j] == '∀':
                    #clause[j] = '∃'
                    clause = clause[:j] + '∃' + clause[j+1:]
                elif clause[j] == '~':
                    #clause[j] = ' '
                    clause = clause[:j] + ' ' + clause[j+1:]
                    if clause[j+1] != '(':
                        j+=1
                elif clause[j] ==']' or clause[j] == ' ' :
                    j=j
                elif clause[j] == '[':
                    j+=1
                elif clause[j] == '(':
                    sums += 1
                elif clause[j] == ')':
                    sums -= 1
                else :
                    clause = clause[:j] + '~'+ clause[j:]
                    j+=1
                j+=1
            i = len(clause)
        i-=1
                    
    return clause
            
                
                    
                
                
            
    


# In[213]:


stat = "~(~(X[a]|Y[b])&Z[c])"
print (f"statment =\n{stat}\nafter apply negation statment\n{apply_negation(stat).replace(' ','')} ")
print("\n--------------------------------------------------------------------\n")
statment = statment.replace(' ','')
print (f"statment =\n{statment}\nafter apply negation statment \n{apply_negation(statment).replace(' ','')} ")
statment = apply_negation(statment).replace(' ','')



# In[214]:


from collections import defaultdict

def standardize_scope(expression):


    variable_map = defaultdict(int)  

    def rename_variables(part):
        if part.startswith("∀") or part.startswith("∃"):
            
            quantifier = part[0]
            variables = part[1:].split()
            if len(variables) == 0:
                return quantifier
            renamed_variables = [f"{var}_{variable_map[var]}" for var in variables]
            return quantifier + " ".join(renamed_variables)
        elif "(" in part:
            index_start = part.find("(")
            index_end = part.find(")")
            return part[:index_start + 1] + rename_variables(part[index_start + 1:index_end]) + part[index_end:]
        else:
            if part.isalpha(): 
                var = part
                variable_map[var] += 1
                return f"{var}_{variable_map[var]}"
            else:
                return part

    return rename_variables(expression)
print(statment)
statment = standardize_scope(statment)[:-2]
print(statment)



# In[215]:


#function 5

def prenex_form (clause) :
    i = 0
    ar = []
    while i < len(clause):
        if clause[i] == '∃' or clause[i] == '∀':
            st= clause[i:i+4]
            ar.append(st)
            clause = clause[:i] + clause[i+4:]
            i=0
        i+=1
    clause = ''.join(ar) + clause
    return clause
            
    
stat = "(∀[x] P[x]) | (∃[y] Q[y])"
stat=stat.replace(" ","")
print (stat)
print(prenex_form(stat))

print (statment)
statment=prenex_form(statment)
print(statment)





# In[216]:


import re


def Skolemization(clause):
    k = 0
    while(k<len(clause)):
        if(clause[k] == ']' and clause[k+1] =='('):
            clause = clause[:k]+' '+clause[k+1:]
            break
        else:
            k+=1
    i = 0
    flag = False
    counter = 1
    new_clause = ""
    while i < len(clause):
        if clause[i] == "∃":
            if flag:
                j = i + 2
                if not bool(new_clause):
                    new_clause = clause.replace(clause[j], "F" + str(counter) + "[x]")
                else:
                    new_clause = new_clause.replace(
                        clause[j], "F" + str(counter) + "[x]"
                    )
                counter += 1
            else:
                j = i + 2
                if not bool(new_clause):
                    new_clause = clause.replace(clause[j], "F" + str(counter))
                else:
                    new_clause = new_clause.replace(clause[j], "F" + str(counter))
            counter += 1
        elif clause[i] == "∀":
            flag = True

        i += 1

    new_clause = new_clause.split()
    temp_pattern = new_clause[0]
    temp = ""
    i = 1
    pattern = r"∀[𝑎-𝑧]"
    matches = re.findall(pattern, temp_pattern)
    filtered_sentence = "".join(matches)
    temp += filtered_sentence
    new_clause.pop(0)
    for i in new_clause:
        temp += i
    return temp


stat1 = "∃[y] (P[A] ∨ Q[y])"
#stat=stat.replace(" ","")
print (stat1)
print(Skolemization(stat1))

print (statment)
statment=Skolemization(statment)
print(statment)


# In[185]:


#function 7
def Drop_universal_quantifiers (clause) :
    i = 0
    while i < len(clause):
        if clause[i] == '∀':
            clause = clause[:i] + clause[i+4:]
            i=0
        i+=1
    return clause

stat = "∀[x] P[x] | Q[F [x]]"
stat=stat.replace(" ","")
print (stat)
print(Drop_universal_quantifiers(stat))

print (statment)
#statment=Skolemization(statment)
print(Drop_universal_quantifiers(statment))
#print(statment)

        
    


# In[217]:


def  Convert_to_conjunctive(clause):
    i = 0
    k=-1
    while i < len(clause):
        if clause[i] == '&':
            k=i
            
        if clause[i:i+2] == '|(':
            stat = clause[i+2:-1]
            clause = clause[1:k] + '|' + stat + '&('+ clause[k+1:i-1]+'|' + stat
        i+=1
    return clause
print (statment)
#statment=Skolemization(statment)
print(Convert_to_conjunctive(statment))
statment =Convert_to_conjunctive(statment)
     


# In[218]:


def conjunctions_into_clauses(clause):
    clause=clause.replace("|",",")
    splitted = clause.split("&")
    for part in splitted:
        print(part.strip())
    return splitted 
ar = conjunctions_into_clauses(statment)
print (ar)


# In[235]:


def rename_variables(clauses):
    str0 = clauses[0]
    str1 = clauses[1]

    str1_modified = str1.replace("F", "A")

    modified_clauses = str0 + ',' + str1_modified

    return modified_clauses

print(rename_variables(ar))


# In[ ]:




