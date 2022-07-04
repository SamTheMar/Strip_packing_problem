import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as patches
import matplotlib.colors as mcolors
from matplotlib.ticker import ScalarFormatter

from os import listdir

from collections import namedtuple

PositionedRectangle = namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
Rectangle = namedtuple('Rectangle', ['w', 'h'])


def read_instance(filename):
    """
    Parameters
    ----------
    filename : string
        file of the instance. Its format is:
        total_width
        n_rectangles
        w_1 h_1
        ......
        w_n h_n

    Returns
    -------
    W : int
        total width of the strip
    n : int
        number of rectangles
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.
    """
    with open(filename, "r") as f:
        content = f.read()

    lines = content.split("\n")
    W = int(lines[0].split(" ")[0])
    n = int(lines[1].split(" ")[0])

    cont = np.asarray([lines[i+2].split(" ") for i in range(n)], dtype=int)

    rectangles = [Rectangle(cont[i, 0], cont[i, 1]) for i in range(len(cont))]

    return W, n, rectangles


def parse_solution(solution_string):
    """
    Parameters
    ----------
    solution_string : string
        string of the solution. Its format is:
        total_width total_height
        n_rectangles
        w_1 h_1 x_1 y_1
        ......
        w_n h_n x_n y_n

    Returns
    -------
    W : int
        total width of the strip
    H : int
        total height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    lines = solution_string.split("\n")
    W, H = (int(x) for x in lines[0].split(" "))
    n = int(lines[1].split(" ")[0])

    cont = np.asarray([lines[i+2].split(" ") for i in range(n)], dtype = int)
    
    rectangles = [PositionedRectangle(cont[i, 2], cont[i, 3], cont[i, 0], cont[i, 1]) for i in range(len(cont))]
    
    return W, H, rectangles


def read_solution(filename):
    """
    Parameters
    ----------
    filename : string
        file of the solution. The file content must respect the format given by parse_solution.

    Returns
    -------
    W : int
        total width of the strip
    H : int
        total height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    with open(filename, "r") as f:
        content = f.read()
    return parse_solution(content)


def save_solution(filename, W, H, rectangles):
    """
    Parameters
    ----------
    filename : string
        absolute or relative path of the solution file
    W : int
        total width of the strip
    H : int
        total height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    with open(filename, "w") as f:
        f.write(f"{W} {H}\n")
        f.write(f"{len(rectangles)}\n")

        for rect in rectangles:
            f.write(f"{rect.w} {rect.h} {rect.x} {rect.y}\n")


def visualize(W, H, rectangles, ax = None, plot_width = 720, dpi = 100, linewidth = 3, show_grid = True, gridwidth = 0.5, gridstyle = '-', show_rectangle_numbering = True, show_info = True, additional_info = ""):
    """
    Visualization of the a strip of size width x height with the layout of the rectangles.
    The rectangles are annotated with their place in the input list on the figure.

    Parameters
    ----------
    W : int
        total width of the strip
    H : int
        total height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    ax : ``matplotlib.axes._subplots.AxesSubplot``, optional
        The axes on which to show the plot
    plot_width : int, default 720
        Plot width in pixels. Used only if ax in not provided.
    dpi : int, default 100
        dpi of the plot figure. Used only if ax in not provided.
    linewidth : float, default 3
        linewidth of the rectangle borders.
    show_grid : bool, default True
    gridwidth : float, default 1
        linewidth of the grid lines. Used only if show_grid is True.
    gridstyle : string, default '-'
    show_rectangle_numbering : bool, default True
        toggle whether to show the number of the rectangle in the lower left corner.
    show_info : bool, default True
        toggle whether to show the width and height of the strip and the number of rectangles on the title.
    additional_info : string, optinal
        Additional information to display on the title.
        Used ony if show_info is True.

    Returns
    -------
    ``matplotlib.figure.Figure``, ``matplotlib.axes._subplots.AxesSubplot``
    """
    if ax == None:
        if W == 0 or H == 0:
            aspect = 1
        else:
            aspect = H/W
        fw, fh = plot_width, plot_width*aspect
        fig, ax = plt.subplots(figsize = (fw/dpi, fh/dpi), dpi = dpi)

    else:
        fig = ax.get_figure()

    colors = list(mcolors.TABLEAU_COLORS.values())

    for idx, r in enumerate(rectangles):
        ax.add_patch(
            patches.Rectangle(
                (r.x, r.y),  # (x,y)
                r.w,  # width
                r.h,  # height
                facecolor = colors[idx%10],
                edgecolor = 'k',
                linewidth = linewidth,
                alpha = 0.8
            )
        )
        if show_rectangle_numbering:
            if W < 15:
                fontsize = 'xx-large'
            elif  W < 20:
                fontsize = 'x-large'
            elif W < 27:
                fontsize = 'large'
            else:
                fontsize = 'medium'

            if not show_grid:
                fontsize = 'xx-large'
            ax.text(r.x + 0.25, r.y + 0.25, str(idx+1), fontsize = fontsize)

    ax.set_xlim(0, W)
    ax.set_ylim(0, H)

    ax.set_xticks(np.arange(W+1))
    ax.set_yticks(np.arange(H+1))

    ax.set_aspect('equal', adjustable='box')
    
    if show_grid:
        ax.grid(color = 'k', ls = gridstyle, linewidth = gridwidth)

    ax.set_facecolor('w')

    for b in ax.spines.values():
        b.set_linewidth(linewidth)

    if show_info:
        if additional_info != "":
            additional_info += ", "
        fig.suptitle(additional_info + f"{len(rectangles)} rectangles, W = {W}, H = {H}")

    fig.tight_layout(pad = 1)

    return fig, ax


def visualize_from_string(solution_string, **kwargs):
    """
    Visualization of the a strip of size width x height with the layout of the rectangles.
    The rectangles are annotated with their place in the input list on the figure.

    Parameters
    ----------
    solution_string : string
        string of the solution. Its format is:
        total_width total_height
        n_rectangles
        w_1 h_1 x_1 y_1
        ......
        w_n h_n x_n y_n
    kwargs : dict
        keyowrd arguments passed to ``visualize``

    Returns
    -------
    ``matplotlib.figure.Figure``, ``matplotlib.axes._subplots.AxesSubplot``
    """
    W, H, rectangles = parse_solution(solution_string)
    fig, ax = visualize(W, H, rectangles, **kwargs)
    return fig, ax


def visualize_from_file(filename, **kwargs):
    """
    Visualization of the a strip of size width x height with the layout of the rectangles.
    The rectangles are annotated with their place in the input list on the figure.
    Parameters
    ----------
    filename : string
        file of the solution. The file content must respect the format given by parse_solution.
    kwargs : dict
        keyowrd arguments passed to ``visualize``

    Returns
    -------
    ``matplotlib.figure.Figure``, ``matplotlib.axes._subplots.AxesSubplot``
    """
    W, H, rectangles = read_solution(filename)
    fig, ax = visualize(W, H, rectangles, **kwargs)
    return fig, ax


def sort_by_area(rectangles, reverse = True):
    """
    sorts rectangles by area in decreasing order. If reverse is False, the sorting is in increasing order.
    """
    areas = [r.w * r.h for r in rectangles]
    _, sorted_rectangles = zip(*sorted(zip(areas, rectangles), reverse = reverse))
    return list(sorted_rectangles)


def write_execution_time(filename, execution_time):
    """
    Write execution time from a single file.
    """
    with open(filename, "a") as f:
        f.write(f"\nexecution time in seconds: {execution_time:.3f}")


def get_execution_time(filename):
    """
    Return execution time from a single file.
    """
    with open(filename, "r") as f:
        content = f.read()
    return float(content.split("\n")[-1].split()[-1])


def get_execution_times(folder, num_instances = 40):
    """
    Return execution times from all files in folder.
    If num_instances is 0, the times of the files are returned.
    Otherwise, if the file of the corresponding instance is not found,
    the time is set to be infinite.
    """
    if num_instances != 0:
        times = np.zeros(num_instances)
        for i in range(num_instances):
            try:
                times[i] = get_execution_time(f"{folder}/ins-{i+1}-sol.txt")
            except:
                times[i] = np.finfo(np.float32).max
    else:
        times = []
        for i, filename in enumerate(listdir(folder)):
            times.append(get_execution_time(f"{folder}/{filename}"))

    return np.asarray(times)


def get_timing_stats(execution_times, timeout = 300):
    """
    Get stats from an array of execution times.
    """
    no_timeout = execution_times < timeout
    stats = {
        'solved instances': no_timeout.sum(),
        'average time (all)':  execution_times.mean(),
        'average time (solved)': execution_times[no_timeout].mean()
    }
    return stats


def make_stats_table(execution_time_data, ax, bbox=(0.05, 0.60, 0.17, 0.17)):
    """
    Make a table on the provided axes with the stats of the execution time for each computation approache.
    """
    spaces = 10
    rows = [' ' * spaces for i in range(len(execution_time_data))]
    rowcolors = [f'C{i}' for i in range(len(execution_time_data))]
    cols = ('Solved \ninstances', 'Average\nruntime')

    stats = [get_timing_stats(execution_times) for execution_times in execution_time_data]
    t = [[f'{s["solved instances"]}/40', f'{s["average time (solved)"]:.2f} s'] for s in stats]
    return ax.table(t, rowLabels=rows, rowColours=rowcolors, colLabels=cols, bbox=bbox)


def visualize_execution_times(data, labels, bar_width=0.3, timeout = 300, ax = None, plot_height = 720, aspect = 16/9, dpi = 100, show_grid = True, show_stats_table = True, title = None):
    """
    Visualize the execution time for multiple computation approaches for each instance.

    Parameters
    ----------
    data : 2D array or array-like
        data with execution time. Its shape mus be (num_approaches, num_instances).
    labels : array or array-like
        list of labels for each computation approach.
    bar_width : float, default 0.3
        width of the bars.
    timeout : int, default 300
        chosen value for the computation timeout in seconds.
    ax : ``matplotlib.axes._subplots.AxesSubplot``, optional
        The axes on which to show the plot
    plot_height : int, default 720
        plot height in pixels
    aspect : float, default 16/9
        aspect ratio of the plot figure.
    dpi : float, default 100
    show_grid : bool, default True
    show_stats_table : bool, default True
    title : string, optional
        Title to display on top of the figure

    Returns
    -------
    ``matplotlib.figure.Figure``, ``matplotlib.axes._subplots.AxesSubplot``
    """
    if ax == None:
        fw, fh = plot_height*aspect, plot_height
        fig, ax = plt.subplots(figsize = (fw/dpi, fh/dpi), dpi = dpi)
    else:
        fig = ax.get_figure()

    ins_number = np.arange(len(data[0]))+1
    ind_done = [np.argwhere(d<=timeout).squeeze() for d in data]
    ind_timeout = [np.argwhere(d>timeout).squeeze() for d in data]

    #TODO: improve this
    offsets = np.linspace(-bar_width/2, bar_width/2, len(data))
    bar_width *= 0.95

    ax.set_yscale('log')

    for i in range(len(data)):
        id = ind_done[i]
        it = ind_timeout[i]
        ax.bar(ins_number[id] + offsets[i], data[i][id], color = f"C{i}", width = bar_width, label = labels[i])
        ax.bar(ins_number[it] + offsets[i], data[i][it], color = f"C{i}", width = bar_width, hatch = '//', alpha = 0.3)

    if show_stats_table: make_stats_table(data, ax)

    ax.set_xlim(0, len(data[0])+1)
    ax.set_xticks(ins_number)

    ax.set_yticks(np.concatenate([ax.get_yticks(), [30, 200, 300]]))
    ax.set_ylim(1e-2, 300)
    ax.get_yaxis().set_major_formatter(ScalarFormatter())

    if show_grid:
        ax.grid(axis = 'y')
    ax.legend()

    if title is not None:
        fig.suptitle(title)
    fig.tight_layout(pad = 0.8)

    return fig, ax
