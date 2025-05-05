import json
import os

#to download your progress, login to the https://quantum.microsoft.com/en-us/tools/quantum-katas and open Network and search for 'katas' XHR json file,then download it

with open('katas.json') as f:
    katas = json.load(f)
    for id_num,kata in enumerate(katas):
        kata_name = kata["kataId"]
        kataId = str(id_num+1)+"_"+kata_name
        print(kataId)
        if not os.path.exists(kataId):
            os.makedirs(kataId)

        for section_name,section_obj in kata["sections"].items():
            code = section_obj["code"] 
            section_name = section_name.strip()
            if code and section_obj["attempts"] != None:
                section_name_parts = section_name.split('__')
                if len(section_name_parts) > 1 and section_name_parts[0] == kata_name:
                    section_name = section_name_parts[1]
                    print(kata_name,section_name)
                else:
                    raise ValueError(f"Section name {section_name} is not valid, it should be kata_name__section_name")
                
                # if os.path.exists(os.path.join(kata_name, section_name)):
                #     os.remove(os.path.join(kata_name, section_name))

                with open(os.path.join(kataId, section_name)+".qs", 'w') as f:
                   f.write(code)



