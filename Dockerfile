# Build with $ podman build --platform linux/amd64 -t syntheos 
# 1. Imagen base con Python 3.13 (podés bajar de versión si no necesitás 3.13)
FROM python:3.13-slim

# 2. Crear y entrar al directorio de trabajo
WORKDIR /syntheos

# 3. Copiar el código de tu proyecto
COPY . /syntheos

# 4. Instalar dependencias (usando requirements.txt)
RUN pip install --no-cache-dir -r requirements.txt

RUN apt-get update && apt-get install -y curl tar && \
    mkdir -p /tmp/strix &&\
    curl -L https://github.com/meyerphi/strix/releases/download/21.0.0/strix-21.0.0-1-x86_64-linux.tar.gz -o /tmp/strix.tar.gz && \
    tar -xzf /tmp/strix.tar.gz -C /tmp && \
    mv /tmp/strix /syntheos/strix && \
    chmod +x /syntheos/strix && \
    rm -rf /tmp/strix*

# 6. Definir punto de entrada (pasará argumentos a syntheos.py)
ENTRYPOINT ["python", "syntheos.py"]
