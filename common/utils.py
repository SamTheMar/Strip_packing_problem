import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as patches

import os

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


def visualize(W, H, rectangles, ax = None, plot_width = 720, dpi = 100, linewidth = 3, grid = True, gridwidth = 0.5, gridstyle = '-', rectangle_numbering = True, axis_off = False, show_info = True, additional_info = ""):
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
    plot_width : int, default: 720
        Plot width in pixels. Used only if ax in not provided.
    dpi : int, default: 100
        dpi of the plot figure. Used only if ax in not provided.
    linewidth : float, default: 3
        linewidth of the rectangle borders.
    grid : bool, default: True
    gridwidth : float, default: 1
        linewidth of the grid lines. Used only if show_grid is True.
    gridstyle : string, default: '-'
    rectangle_numbering : bool, default: True
        toggle whether to show the number of the rectangle in the lower left corner.
    axis_off : bool, default: False
        turn off the axis.
    show_info : bool, default: True
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

    for idx, r in enumerate(rectangles):
        ax.add_patch(
            patches.Rectangle(
                (r.x, r.y),  # (x,y)
                r.w,  # width
                r.h,  # height
                facecolor = f"C{idx}",
                edgecolor = 'k',
                linewidth = linewidth,
                alpha = 0.8
            )
        )
        if rectangle_numbering:
            if W < 15:
                fontsize = 'xx-large'
            elif  W < 20:
                fontsize = 'x-large'
            elif W < 27:
                fontsize = 'large'
            else:
                fontsize = 'medium'

            if not grid:
                fontsize = 'xx-large'
            ax.text(r.x + 0.25, r.y + 0.25, str(idx+1), fontsize = fontsize)

    ax.set_xlim(0, W)
    ax.set_ylim(0, H)

    ax.set_xticks(np.arange(W+1))
    ax.set_yticks(np.arange(H+1))

    ax.set_aspect('equal', adjustable='box')
    
    if grid:
        ax.grid(color = 'k', ls = gridstyle, linewidth = gridwidth)

    ax.set_facecolor('w')

    for b in ax.spines.values():
        b.set_linewidth(linewidth)

    if show_info:
        if additional_info != "":
            additional_info += ", "
        fig.suptitle(additional_info + f"{len(rectangles)} rectangles, W = {W}, H = {H}")

    fig.tight_layout(pad = 1)
    if axis_off:
        ax.set_axis_off()
        if not show_info:
            fig.tight_layout(pad = 0)

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


def generate_plots_from_files(input_folder, output_folder = None, show_plots = True, plot_format = ['png'], *args, **kwargs):
    """
    Generate plots from the solution files in the provided folder.

    Parameters
    ----------
    input_folder : str
    output_folder : str, optional
        folder where to save the plots. If not provided, the plots will not be saved.
    show_plots : bool, default: True
        Toggle whether to show the plots in the output.
    plot_formats : string or list of string, optional
        format in which to save the plots.
    *args, **kwargs
        attitional arguments are passed to ``visualize_from_file``
    """
    filenames = os.listdir(input_folder)
    instance_numbers = [int(name.split("-")[1]) for name in filenames]
    _, filenames = zip(*sorted(zip(instance_numbers, filenames)))

    for filename in filenames:
        instance_name = "-".join(filename.split(".")[0].split("-")[:-1])
        fig, ax = visualize_from_file(os.path.join(input_folder, filename), additional_info = instance_name, *args, **kwargs)
        if output_folder is not None:
            if not os.path.isdir(output_folder): os.makedirs(output_folder)
            if type(plot_format) == str:
                fig.savefig(os.path.join(output_folder,filename.split(".")[0]) + '.' + plot_format)
            else:
                for f in plot_format:
                    fig.savefig(os.path.join(output_folder,filename.split(".")[0]) + '.' + f)
        if show_plots:
            plt.show()
            print(150*"=")
        else:
            plt.close(fig)


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
    if not os.path.isfile(filename):
        print("ERROR: File does not exist")
        return
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
        for i, filename in enumerate(os.listdir(folder)):
            times.append(get_execution_time(f"{folder}/{filename}"))

    return np.asarray(times)


def geometric_mean(x):
    a = np.log(x)
    return np.exp(a.mean())


def get_timing_stats(execution_times, baseline_times = None, timeout = 300):
    """
    Get stats from an array of execution times.
    """
    no_timeout = execution_times < timeout
    stats = {
        'solved instances': no_timeout.sum(),
        'average time (all)':  execution_times.mean(),
        'average time (solved)': execution_times[no_timeout].mean()
    }
    if baseline_times is None:
        return stats
    
    no_timeout = no_timeout & (baseline_times < timeout)
    stats['mean relative runtime'] = geometric_mean(execution_times[no_timeout]/baseline_times[no_timeout])
    return stats


def make_stats_table_with_baseline(execution_time_data, ax, bbox, bar_colors):
    """
    Make a table on the provided axes with the stats of the execution time for each computation approach.
    The first set of times is used as a baseline for the other ones. The geometric mean of the ratio between the baseline times
    and the other ones is shown.
    """
    baseline_times = execution_time_data[0]
    spaces = 3
    rows = [' ' * spaces for i in range(len(execution_time_data))]
    cols = ('Solved \ninstances', 'Mean rel.\nruntime', 'Average\nruntime')

    stats = [get_timing_stats(execution_times, baseline_times) for execution_times in execution_time_data]
    t = [[f"{s['solved instances']}/40", f"{s['mean relative runtime']:.2f}", f"{s['average time (solved)']:.2f} s"] for s in stats]
    table = ax.table(t, rowLabels=rows, alpha = 1, rowColours=bar_colors, colLabels=cols, bbox=bbox, cellLoc = 'center')
    table.set_zorder(200)


def make_stats_table(execution_time_data, ax, bbox, bar_colors):
    """
    Make a table on the provided axes with the stats of the execution time for each computation approach.
    """
    spaces = 6
    rows = [' ' * spaces for i in range(len(execution_time_data))]
    cols = ('Solved \ninstances', 'Average\nruntime')

    stats = [get_timing_stats(execution_times) for execution_times in execution_time_data]
    t = [[f'{s["solved instances"]}/40', f'{s["average time (solved)"]:.2f} s'] for s in stats]
    table = ax.table(t, rowLabels=rows, alpha = 1, rowColours=bar_colors, colLabels=cols, bbox=bbox, cellLoc = 'center')
    table.set_zorder(200)


def visualize_execution_times(data,
                              labels = None,
                              title = None,
                              timeout = 300,
                              instance_labels = None,
                              show_stats_table = True,
                              first_is_baseline = False,
                              show_grid = True,
                              label_axis = True,
                              ax = None,
                              bar_width=-1,
                              bar_clearance = 0.95,
                              plot_height = 720,
                              aspect = 16/9,
                              dpi = 100,
                              stats_table_bbox=(0.03, 0.5, 0.17, 0.3),
                              bar_colors = None,
                              starting_color = 0):
    """
    Visualize the execution time for multiple computation approaches for each instance.

    Parameters
    ----------
    data : 2D array or array-like
        Data with execution time. Its shape must be (num_approaches, num_instances).
    labels : array or array-like, optional
        List of labels for each computation approach.
    title : string, optional
        Title to display on top of the figure.
    timeout : int, default: 300
        Chosen value for the computation timeout in seconds.
    instance_labels : array or array-like, optional
        Array of instance labels. If not provided, the instances are progressively numbered starting with 1.
    show_stats_table : bool, default: True
    first_is_baseline : bool, default: False
        If True, the first given times are used as a baseline with which to compare the other computation times.
        It shows the geometric mean of the ratio between the baseline times and the other times in the stats table.
        Useful only if ``show_stats_table`` is True.
    show_grid : bool, default: True
    label_axis : bool, default: True,
        Show labels on axes.
    ax : ``matplotlib.axes._subplots.AxesSubplot``, optional
        The axes on which to show the plot.
    bar_width : float, optional
        Total width of all the bars for the same value. Defaults to 0.9 if ``num_approaches`` is 1, 0.6 otherwise.
    bar_clearance : float, default: 0.95
        Clearence between the bars for the same value. Useful only if ``num_approaches`` is greater than 1.
    plot_height : int, default: 720
        Plot height in pixels. Useful only if ``ax`` is not provided.
    aspect : float, default: 16/9
        Aspect ratio of the plot figure. Useful only if ``ax`` is not provided.
    dpi : float, default: 100
        Useful only if ``ax`` is not provided.
    stats_table_bbox : tuple, default: (0.03, 0.5, 0.17, 0.3)
        Bounding box of the stats table. It is a tuple in the form (x_pos, y_pos, width, height).
    bar_colors : list of colors, optional
        colors of the bars.
    starting_color : int, default: 0
        Starting matplotlib color for the bars. Overridden if bar-colors is provided.


    Returns
    -------
    ``matplotlib.figure.Figure``, ``matplotlib.axes._subplots.AxesSubplot``
    """
    if ax == None:
        fw, fh = plot_height*aspect, plot_height
        fig, ax = plt.subplots(figsize = (fw/dpi, fh/dpi), dpi = dpi)
    else:
        fig = ax.get_figure()

    # set logarithmic scale
    ax.set_yscale('log')

    # 
    n_approaches, n_instances = np.shape(data)
    instance_indices = np.arange(n_instances)+1
    indices_done = [np.argwhere(d<=timeout).squeeze() for d in data]
    indices_timeout = [np.argwhere(d>timeout).squeeze() for d in data]

    # set bar widths and offsets
    if bar_width == -1:
        if n_approaches == 1:
            bar_width = 0.9
        else:
            bar_width = 0.6
    offsets = ((np.arange(n_approaches)-(n_approaches-1)/2)/n_approaches)*bar_width
    if n_approaches == 1:
        final_bar_width = bar_width
    else:
        final_bar_width = bar_clearance*bar_width/n_approaches

    # handle labels
    draw_legend = labels is not None
    if not draw_legend:
        labels = [i for i in range(n_approaches)]

    # set bar colors
    if bar_colors is None:
        bar_colors = [f"C{(i+starting_color)%10}" for i in range(n_approaches)]

    # draw bars
    for i in range(n_approaches):
        id = indices_done[i]
        it = indices_timeout[i]
        ax.bar(instance_indices[id] + offsets[i], data[i][id], color = bar_colors[i], width = final_bar_width, label = labels[i])
        ax.bar(instance_indices[it] + offsets[i], data[i][it], color = bar_colors[i], edgecolor = 'k', width = final_bar_width, hatch = '/////', alpha = 0.25)

    # setup axis labelling
    ax.set_xlim(0, n_instances+1)
    ax.set_xticks(instance_indices)
    if instance_labels is not None:
        ax.set_xticklabels(instance_labels[:n_instances])

    ax.set_ylim(1e-2, timeout)

    if label_axis:
        ax.set_xlabel("Instance number")
        ax.set_ylabel("Computation time in seconds")

    # draw grid, stats and legend
    if show_grid:
        ax.set_axisbelow(True)
        ax.grid(axis = 'y', zorder = 0)

    if show_stats_table:
        if first_is_baseline:
            make_stats_table_with_baseline(data, ax, stats_table_bbox, bar_colors)
        else:
            make_stats_table(data, ax, stats_table_bbox, bar_colors)

    if draw_legend: ax.legend()

    if title is not None:
        ax.set_title(title)
    fig.tight_layout(pad = 0.8)

    return fig, ax


def visualize_execution_times_two_plots(data_upper,
                                        data_lower,
                                        axs = [],
                                        plot_height = 720,
                                        aspect = 16/9,
                                        dpi = 100,
                                        hspace = 0.1,
                                        suptitle = None,
                                        kw_upper = {},
                                        kw_lower = {}):
    """
    Visualize the execution time for multiple computation approaches for each instance on two plots, with the lower one having inverted bars.

    Parameters
    ----------
    data_upper : 2D array or array-like
        Data with execution time. Its shape must be (num_approaches, num_instances). Shown in the upper plot.
    data_lower : 2D array or array-like
        Data with execution time. Its shape must be (num_approaches, num_instances). Shown in the lower plot.
    axs : list of ``matplotlib.axes._subplots.AxesSubplot``, optional
        The axes on which to show the plot.
    plot_height : int, default: 720
        Plot height in pixels. Useful only if ``ax`` is not provided.
    aspect : float, default: 16/9
        Aspect ratio of the plot figure. Useful only if ``ax`` is not provided.
    dpi : float, default: 100
        Useful only if ``ax`` is not provided.
    hspace: float, default: 0.1
        parameter passed to ``fig.subplots_adjust``
    suptitle : string, optional
        Title to display on top of the figure.
    kw_upper : dict, optional
        Dictionary of keyword arguments for the upper plot, passed to ``visualize_execution_times``.
    kw_lower : dict, optional
        Dictionary of keyword arguments for the lower plot, passed to ``visualize_execution_times``.

    Returns
    -------
    ``matplotlib.figure.Figure``, ``matplotlib.axes._subplots.AxesSubplot``
    """
    if len(axs) == 0:
        fw, fh = plot_height*aspect, plot_height
        fig, axs = plt.subplots(nrows = 2, figsize = (fw/dpi, fh/dpi), dpi = dpi, sharex = True)

    ax1, ax2 = axs

    if "stats_table_bbox" not in kw_upper.keys():
        kw_upper["stats_table_bbox"] = (0.05, 0.6, 0.17, 0.35)
    if "stats_table_bbox" not in kw_lower.keys():
        kw_lower["stats_table_bbox"] = (0.05, 0.05, 0.17, 0.35)

    visualize_execution_times(data_upper, ax = ax1, label_axis=False, **kw_upper)
    visualize_execution_times(data_lower, ax = ax2, **kw_lower)
    ax2.invert_yaxis()

    if suptitle is not None:
        fig.suptitle(suptitle)

    fig.tight_layout()
    fig.subplots_adjust(hspace=hspace)

    return fig, axs
