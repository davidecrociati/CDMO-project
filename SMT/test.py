import threading
import queue
import time
import random
import signal
import functools

# Timeout decorator function
def timeout(seconds=5, default=None):
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            # Only use signal if in the main thread
            def handle_timeout(signum, frame):
                raise TimeoutError()
            
            signal.signal(signal.SIGABRT, handle_timeout)
            signal.alarm(seconds)
            
            try:
                result = func(*args, **kwargs)
            except TimeoutError:
                result = default
            finally:
                signal.alarm(0)
            
            return result
        
        return wrapper
    
    return decorator

# Use the timeout decorator for the solver function
@timeout(seconds=5, default=None)
def solver():
    # Simulate work with a random sleep
    sleep_time = random.uniform(0.1, 1.0)  # Random sleep between 0.1 and 1.0 seconds
    time.sleep(sleep_time)
    n=random.randint(1, 100)
    print(n)
    return  n # Return a random integer as a solution

# Launcher function to manage the solver and store solutions
def launcher():
    # Time limit for the launcher
    runtime = 10  # seconds
    
    # Queue to store solutions
    solution_queue = queue.Queue()
    st=time.time()
    # Function to run the solver and put solutions in the queue
    def worker():
        start_time = time.time()
        while time.time() - start_time < runtime:
            try:
                result = solver()
                if result is not None:
                    solution_queue.put(result)
            except TimeoutError:
                continue
    
    # Create and start threads
    threads = []
    for _ in range(1):  # Number of solver threads
        thread = threading.Thread(target=worker)
        thread.start()
        threads.append(thread)
    
    # Wait for all threads to finish
    for thread in threads:
        thread.join()
    
    # Retrieve all solutions
    solutions = []
    while not solution_queue.empty():
        solutions.append(solution_queue.get())
    
    # Print the number of solutions and some example solutions
    print(f"Number of solutions collected: {len(solutions)}")
    print(f"Example solutions: {solutions[:10]}")  # Show up to 10 solutions
    print(time.time()-st)
# Run the launcher function
if __name__ == "__main__":
    launcher()
