FROM minizinc/minizinc:latest

WORKDIR ./project

COPY . .

RUN apt-get update 
RUN apt-get install -y python3 
RUN apt-get install -y python3-pip 
RUN apt-get install -y minizinc 

# FIXME : Non riesce a scaricare i moduli tramite equirements
RUN python3-pip install -r requirements.txt 
# CMD pip install -r requirements.txt --break-system-packages  <------ alternativa (bruttina)

# Per automatizzare la procedura magari fare uno script launcher.sh
CMD python3 CP/CP_launcher.py