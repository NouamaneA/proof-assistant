CAMLC = ocamlopt

TARGET = prover

all: $(TARGET)

$(TARGET): $(TARGET).ml
	$(CAMLC) $(TARGET).ml -o $(TARGET)

clean:
	rm -f $(TARGET) $(TARGET).o $(TARGET).cm[ix]