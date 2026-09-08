# 569/A — Music

*Rating:* 1500 · *Limits:* 2.0s, 256.0 MB · *Tags:* implementation, math

## Description

Little Lesha loves listening to music via his smartphone. But the smartphone doesn't have much memory, so Lesha listens to his favorite songs in a well-known social network InTalk.

Unfortunately, internet is not that fast in the city of Ekaterinozavodsk and the song takes a lot of time to download. But Lesha is quite impatient. The song's duration is T seconds. Lesha downloads the first S seconds of the song and plays it. When the playback reaches the point that has not yet been downloaded, Lesha immediately plays the song from the start (the loaded part of the song stays in his phone, and the download is continued from the same place), and it happens until the song is downloaded completely and Lesha listens to it to the end. For q seconds of real time the Internet allows you to download q - 1 seconds of the track.

Tell Lesha, for how many times he will start the song, including the very first start.

## Input

The single line contains three integers T, S, q (2 ≤ q ≤ 104, 1 ≤ S < T ≤ 105).

## Output

Print a single integer — the number of times the song will be restarted.

## Note

In the first test, the song is played twice faster than it is downloaded, which means that during four first seconds Lesha reaches the moment that has not been downloaded, and starts the song again. After another two seconds, the song is downloaded completely, and thus, Lesha starts the song twice.

In the second test, the song is almost downloaded, and Lesha will start it only once.

In the third sample test the download finishes and Lesha finishes listening at the same moment. Note that song isn't restarted in this case.

## Examples

*Example 1 — input:*
```
5 2 2
```

*Example 1 — output:*
```
2
```

*Example 2 — input:*
```
5 4 7
```

*Example 2 — output:*
```
1
```

*Example 3 — input:*
```
6 2 3
```

*Example 3 — output:*
```
1
```
