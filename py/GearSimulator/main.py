import multiprocessing

from app.gui import main


if __name__ == "__main__":
    multiprocessing.freeze_support()
    main()
