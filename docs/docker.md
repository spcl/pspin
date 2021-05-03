This is the fastest way to try out PsPIN. The latest PsPIN Docker image is available on the GitHub Container Registry. You can pull and try existing handlers or directly test your own ones. The image also contains the enviroment to verilate the hardware: you can keep using it as development environment if you make changes to the hardware or pull yet unreleased updates.

### Pull the image

```bash
docker pull ghcr.io/spcl/pspin:latest
```

### Get a shell into the container

```bash
docker run -it ghcr.io/spcl/pspin:latest /bin/bash
```

### Setup enviroment

```bash
source pspin/sourceme.sh
```

### Run examples

```bash
cd pspin/examples/pingpong
make deploy
make driver
make run
```

### Run your own handlers
Remember that changes made inside the container are not persistent! If you are working on your own handlers and want to test them inside the container, then you need to mount your working directory:

```bash
docker run -v <host working dir>:<container working dir> -it ghcr.io/spcl/pspin:latest /bin/bash
```
