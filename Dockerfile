FROM minizinc/minizinc:latest

WORKDIR /project

COPY . .

# Install necessary packages
RUN apt-get update \
    && apt-get install -y python3 \
    && apt-get install -y python3-pip \
    && python3 -m pip install -r requirements.txt --break-system-packages \
    && rm -rf /var/lib/apt/lists/*

# As default prints the help 
RUN echo 'python3 /project/main2.py -h' >> /root/.bashrc

# In order to use the image
## docker build . -t <image_name> -f Dockerfile
## docker run -it <image_name> /bin/bash