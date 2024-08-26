FROM minizinc/minizinc:latest

WORKDIR /project

# Copy all the project
COPY . .

# Install necessary packages
RUN apt-get update \
    && apt-get install -y python3 \
    && apt-get install -y python3-pip\
    && python3 -m pip install -r requirements.txt --break-system-packages

# In order to build and run the docker image, in the local machine exec:
# docker build . -t <image_name> -f Dockerfile
# docker run -it <image_name> /bin/bash

# In order to exec teh project
# python3 main.py ...