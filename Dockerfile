FROM minizinc/minizinc:latest

WORKDIR /project

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
# Copy the launcher.sh script into the /app directory in the image
COPY launcher.sh .

# Ensure the script has the correct line endings (optional, if developing on Windows)
RUN apt-get update && apt-get install -y dos2unix && dos2unix launcher.sh

# Make the script executable
RUN chmod +x launcher.sh

# Run the script
CMD ["./launcher.sh"]