# Include official Isabelle Docker image
FROM makarius/isabelle:Isabelle2021

# Copy files -- the checkout action cannot run as the isabelle user
COPY . ./