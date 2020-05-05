LP_SRC = $(shell find . -type f -name "*.lp")
LP_OBJ = $(LP_SRC:%.lp=%.lpo)

all: $(LP_OBJ)

$(LP_OBJ)&: $(LP_SRC)
	lambdapi check --gen-obj $^

install: $(LP_OBJ) lambdapi.pkg
	lambdapi install lambdapi.pkg $(LP_OBJ) $(LP_SRC)

uninstall:
	lambdapi uninstall lambdapi.pkg

clean:
	rm -f $(LP_OBJ)
