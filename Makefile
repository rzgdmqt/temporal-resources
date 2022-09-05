default: all

all: 
	agda Everything.agda

time:
	time agda Everything.agda

clean:
	find . -name "*.agdai" -type f -delete
