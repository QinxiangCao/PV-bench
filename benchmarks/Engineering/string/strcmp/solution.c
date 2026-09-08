int strcmp(char *s1, char *s2)

{
  int i = 0;

  while (s1[i] != 0 && s1[i] == s2[i]) {
    i++;
  }
  return s1[i] - s2[i];
}

int strncmp(char *s1, char *s2, int n)

{
  int i = 0;

  while (i < n && s1[i] != 0 && s1[i] == s2[i]) {
    i++;
  }
  if (i == n) {
    return 0;
  }
  return s1[i] - s2[i];
}

