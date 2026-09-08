# 245/B — Internet Address

*Rating:* 1100 · *Limits:* 2.0s, 256.0 MB · *Tags:* implementation, strings

## Description

Vasya is an active Internet user. One day he came across an Internet resource he liked, so he wrote its address in the notebook. We know that the address of the written resource has format:

<protocol>://<domain>.ru[/<context>]

where:

- <protocol> can equal either "http" (without the quotes) or "ftp" (without the quotes),
- <domain> is a non-empty string, consisting of lowercase English letters,
- the /<context> part may not be present. If it is present, then <context> is a non-empty string, consisting of lowercase English letters.

If string <context> isn't present in the address, then the additional character "/" isn't written. Thus, the address has either two characters "/" (the ones that go before the domain), or three (an extra one in front of the context).

When the boy came home, he found out that the address he wrote in his notebook had no punctuation marks. Vasya must have been in a lot of hurry and didn't write characters ":", "/", ".".

Help Vasya to restore the possible address of the recorded Internet resource.

## Input

The first line contains a non-empty string that Vasya wrote out in his notebook. This line consists of lowercase English letters only.

It is guaranteed that the given string contains at most 50 letters. It is guaranteed that the given string can be obtained from some correct Internet resource address, described above.

## Output

Print a single line — the address of the Internet resource that Vasya liked. If there are several addresses that meet the problem limitations, you are allowed to print any of them.

## Note

In the second sample there are two more possible answers: "ftp://httpruru.ru" and "ftp://httpru.ru/ru".

## Examples

*Example 1 — input:*
```
httpsunrux
```

*Example 1 — output:*
```
http://sun.ru/x
```

*Example 2 — input:*
```
ftphttprururu
```

*Example 2 — output:*
```
ftp://http.ru/ruru
```
