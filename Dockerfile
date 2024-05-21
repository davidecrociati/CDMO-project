FROM minizinc/minizinc:latest

WORKDIR ./project

COPY . .

# TODO: aggiungere dipendenze
# RUN apt-get update 
# RUN apt-get install -y python3 
# RUN apt-get install -y python3-pip 
# RUN apt-get install -y minizinc 

# FIXME : Dà errore
# RUN python3-pip install -r requirements.txt 
# CMD pip install -r requirements.txt --break-system-packages  <------ alternativa (bruttina)

# docker build . -t <nome_immagine> -f Dockerfile
# docker run -i <nome_immagine>
CMD ./launcher.sh