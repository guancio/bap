SOURCES := test.c

# Objs are all the sources, with .c replaced by .o
OBJS := $(SOURCES:.c=.o)

all: t

# Compile the binary 't' by calling the compiler with cflags, lflags, and any libs (if defined) and the list of objects.
t: $(OBJS)
    $(CC) $(CFLAGS) -o t $(OBJS) $(LFLAGS) $(LIBS)

# Get a .o from a .cpp by calling compiler with cflags and includes (if defined)
.cpp.o:
    $(CC) $(CFLAGS) $(INCLUDES) -c $<
