SOURCE=map.c
TARGET=map

CFLAGS = -I. -std=gnu17 -g

all: $(TARGET)

cov: $(TARGET)-cov

$(TARGET): $(SOURCE)
	gcc $(CFLAGS) -o $@ -I. $^

$(TARGET)-cov: $(SOURCE)
	gcc $(CFLAGS) --coverage -o $(TARGET) -I. $^

run:
	./$(TARGET)

valgrind:
	valgrind ./$(TARGET)

gcov: cov
	valgrind ./$(TARGET)
	lcov -t "$(TARGET)" -o $(TARGET).info -c -d .
	genhtml -o $(TARGET)-lcov-report $(TARGET).info

clean:
	rm -rf $(TARGET) $(TARGET).gcno $(TARGET).gcda $(TARGET).info $(TARGET)-lcov-report

