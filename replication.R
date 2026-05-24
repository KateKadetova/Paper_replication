# ============================================================
# Chen and Li (2009), "Group Identity and Social Preferences"
# Группа: Кадетова, Новикова, Худокормова
# Скрипт для репликации: Рисунок 1, Таблицы 1-7 (реплицировали все из основного текста, не включая приложение)
# ============================================================

# -----------------------------
# 0. Загружаем основные пакеты и читаем данные с файлов
# -----------------------------
packages <- c(
  "haven", "dplyr", "tidyr", "tibble", "sandwich", "lmtest",
  "MASS", "ggplot2", "patchwork", "writexl"
)
to_install <- packages[!packages %in% installed.packages()[, "Package"]]
if (length(to_install) > 0) install.packages(to_install)
 
library(haven)
library(dplyr)
library(tidyr)
library(tibble)
library(sandwich)
library(lmtest)
library(MASS)
library(ggplot2)
library(patchwork)

behavior_path <- "/content/20061107_data_behavior_Chen_Li.dta"
survey_path   <- "/content/20061107_data_survey_Chen_Li.dta"

output_dir <- "outputs"
dir.create(output_dir, showWarnings = FALSE)

behavior <- read_dta(behavior_path)
survey   <- read_dta(survey_path)

# -----------------------------
# 1. Вводим вспомогательные функции
# -----------------------------
cluster_vcov <- function(model, cluster, type = "HC1") {
  sandwich::vcovCL(model, cluster = cluster, type = type)
}

num_grad <- function(f, beta_hat, eps = 1e-6) {
  grad <- numeric(length(beta_hat))
  names(grad) <- names(beta_hat)
  for (j in seq_along(beta_hat)) {
    b_up <- beta_hat
    b_dn <- beta_hat
    b_up[j] <- b_up[j] + eps
    b_dn[j] <- b_dn[j] - eps
    grad[j] <- (f(b_up) - f(b_dn)) / (2 * eps)
  }
  grad
}

ratio_se <- function(model, num, den) {
  b <- coef(model)
  V <- vcov(model)
  ratio <- unname(b[num] / b[den])
  var_ratio <-
    (b[num]^2) * V[den, den] / (b[den]^4) +
    V[num, num] / (b[den]^2) -
    2 * b[num] * V[num, den] / (b[den]^3)
  se <- sqrt(var_ratio)
  tibble(estimate = ratio, std_error = se, t_stat = ratio / se)
}

cluster_reg_p_one_sided <- function(data, formula, cluster_var, coef_name,
                                    alternative = c("greater", "less")) {
  alternative <- match.arg(alternative)
  m <- lm(formula, data = data)
  V <- sandwich::vcovCL(m, cluster = data[[cluster_var]], type = "HC1")
  b <- coef(m)[coef_name]
  se <- sqrt(diag(V))[coef_name]
  z <- b / se
  if (alternative == "greater") {
    pnorm(z, lower.tail = FALSE)
  } else {
    pnorm(z, lower.tail = TRUE)
  }
}

format_mean_n <- function(x, n, digits = 1) {
  paste0(round(x, digits), " [", n, "]")
}

coef_se <- function(est, se, digits = 3) {
  paste0(round(est, digits), " (", round(se, digits), ")")
}

stars <- function(p) {
  case_when(
    p < 0.01 ~ "***",
    p < 0.05 ~ "**",
    p < 0.10 ~ "*",
    TRUE ~ ""
  )
}

logit_me_at_means <- function(model, data, vars, cluster_var, dummy_vars = character()) {
  V <- cluster_vcov(model, data[[cluster_var]])
  beta_hat <- coef(model)
  X <- model.matrix(model)
  xbar <- colMeans(X)
  bind_rows(lapply(vars, function(v) {
    f <- function(beta) {
      xb <- sum(xbar[names(beta)] * beta)
      p <- plogis(xb)
      if (v %in% dummy_vars) {
        x1 <- xbar[names(beta)]
        x0 <- xbar[names(beta)]
        x1[v] <- 1
        x0[v] <- 0
        return(plogis(sum(x1 * beta)) - plogis(sum(x0 * beta)))
      }
      p * (1 - p) * beta[v]
    }
    est <- f(beta_hat)
    grad <- num_grad(f, beta_hat)
    se <- sqrt(drop(t(grad) %*% V %*% grad))
    tibble(variable = v, estimate = est, std_error = se,
           p_value = 2 * pnorm(abs(est / se), lower.tail = FALSE))
  }))
}

logit_me_interaction_table3 <- function(model, data, cluster_var,
                                        y_type = c("positive", "negative")) {
  y_type <- match.arg(y_type)
  V <- cluster_vcov(model, data[[cluster_var]])
  beta_hat <- coef(model)
  means <- data %>%
    summarise(
      ingr = mean(ingr, na.rm = TRUE),
      cost = mean(cost, na.rm = TRUE),
      benefitA = if ("benefitA" %in% names(data)) mean(benefitA, na.rm = TRUE) else NA_real_,
      Bbehind = if ("Bbehind" %in% names(data)) mean(Bbehind, na.rm = TRUE) else NA_real_,
      damageA = if ("damageA" %in% names(data)) mean(damageA, na.rm = TRUE) else NA_real_,
      Bahead = if ("Bahead" %in% names(data)) mean(Bahead, na.rm = TRUE) else NA_real_
    )

  logistic_deriv <- function(xb) {
    p <- plogis(xb)
    p * (1 - p)
  }

  f_one <- function(beta, varname) {
    if (y_type == "positive") {
      m_ingr <- means$ingr; m_cost <- means$cost
      m_benefit <- means$benefitA; m_behind <- means$Bbehind
      xb <- beta["(Intercept)"] + beta["ingr"] * m_ingr + beta["cost"] * m_cost +
        beta["benefitA"] * m_benefit + beta["Bbehind"] * m_behind +
        beta["cost_ingr"] * m_cost * m_ingr +
        beta["benefitA_ingr"] * m_benefit * m_ingr +
        beta["Bbehind_ingr"] * m_behind * m_ingr
      xb1 <- beta["(Intercept)"] + beta["ingr"] +
        (beta["cost"] + beta["cost_ingr"]) * m_cost +
        (beta["benefitA"] + beta["benefitA_ingr"]) * m_benefit +
        (beta["Bbehind"] + beta["Bbehind_ingr"]) * m_behind
      xb0 <- beta["(Intercept)"] + beta["cost"] * m_cost +
        beta["benefitA"] * m_benefit + beta["Bbehind"] * m_behind
      xb1_ingr <- beta["(Intercept)"] + beta["ingr"] +
        beta["cost"] * m_cost + beta["benefitA"] * m_benefit +
        beta["Bbehind"] * m_behind + beta["cost_ingr"] * m_cost * m_ingr +
        beta["benefitA_ingr"] * m_benefit * m_ingr +
        beta["Bbehind_ingr"] * m_behind * m_ingr
      xb0_ingr <- beta["(Intercept)"] + beta["cost"] * m_cost +
        beta["benefitA"] * m_benefit + beta["Bbehind"] * m_behind +
        beta["cost_ingr"] * m_cost * m_ingr +
        beta["benefitA_ingr"] * m_benefit * m_ingr +
        beta["Bbehind_ingr"] * m_behind * m_ingr

      if (varname == "ingr") return(plogis(xb1_ingr) - plogis(xb0_ingr))
      if (varname == "cost") return(beta["cost"] * logistic_deriv(xb))
      if (varname == "benefitA") return(beta["benefitA"] * logistic_deriv(xb))
      if (varname == "Bbehind") return(beta["Bbehind"] * logistic_deriv(xb))
      if (varname == "cost_ingr") return((beta["cost"] + beta["cost_ingr"]) * logistic_deriv(xb1) - beta["cost"] * logistic_deriv(xb0))
      if (varname == "benefitA_ingr") return((beta["benefitA"] + beta["benefitA_ingr"]) * logistic_deriv(xb1) - beta["benefitA"] * logistic_deriv(xb0))
      if (varname == "Bbehind_ingr") return((beta["Bbehind"] + beta["Bbehind_ingr"]) * logistic_deriv(xb1) - beta["benefitA"] * logistic_deriv(xb0))
    }

    if (y_type == "negative") {
      m_ingr <- means$ingr; m_cost <- means$cost
      m_damage <- means$damageA; m_ahead <- means$Bahead
      xb <- beta["(Intercept)"] + beta["ingr"] * m_ingr + beta["cost"] * m_cost +
        beta["damageA"] * m_damage + beta["Bahead"] * m_ahead +
        beta["cost_ingr"] * m_cost * m_ingr +
        beta["damageA_ingr"] * m_damage * m_ingr +
        beta["Bahead_ingr"] * m_ahead * m_ingr
      xb1 <- beta["(Intercept)"] + beta["ingr"] +
        (beta["cost"] + beta["cost_ingr"]) * m_cost +
        (beta["damageA"] + beta["damageA_ingr"]) * m_damage +
        (beta["Bahead"] + beta["Bahead_ingr"]) * m_ahead
      xb0 <- beta["(Intercept)"] + beta["cost"] * m_cost +
        beta["damageA"] * m_damage + beta["Bahead"] * m_ahead
      xb1_ingr <- beta["(Intercept)"] + beta["ingr"] + beta["cost"] * m_cost +
        beta["damageA"] * m_damage + beta["Bahead"] * m_ahead +
        beta["cost_ingr"] * m_cost * m_ingr +
        beta["damageA_ingr"] * m_damage * m_ingr +
        beta["Bahead_ingr"] * m_ahead * m_ingr
      xb0_ingr <- beta["(Intercept)"] + beta["cost"] * m_cost +
        beta["damageA"] * m_damage + beta["Bahead"] * m_ahead +
        beta["cost_ingr"] * m_cost * m_ingr +
        beta["damageA_ingr"] * m_damage * m_ingr +
        beta["Bahead_ingr"] * m_ahead * m_ingr

      if (varname == "ingr") return(plogis(xb1_ingr) - plogis(xb0_ingr))
      if (varname == "cost") return(beta["cost"] * logistic_deriv(xb))
      if (varname == "damageA") return(beta["damageA"] * logistic_deriv(xb))
      if (varname == "Bahead") return(beta["Bahead"] * logistic_deriv(xb))
      if (varname == "cost_ingr") return((beta["cost"] + beta["cost_ingr"]) * logistic_deriv(xb1) - beta["cost"] * logistic_deriv(xb0))
      if (varname == "damageA_ingr") return((beta["damageA"] + beta["damageA_ingr"]) * logistic_deriv(xb1) - beta["damageA"] * logistic_deriv(xb0))
      if (varname == "Bahead_ingr") return((beta["Bahead"] + beta["Bahead_ingr"]) * logistic_deriv(xb1) - beta["damageA"] * logistic_deriv(xb0))
    }
    stop("Unknown variable: ", varname)
  }

  vars <- if (y_type == "positive") {
    c("ingr", "cost", "benefitA", "Bbehind", "cost_ingr", "benefitA_ingr", "Bbehind_ingr")
  } else {
    c("ingr", "cost", "damageA", "Bahead", "cost_ingr", "damageA_ingr", "Bahead_ingr")
  }

  bind_rows(lapply(vars, function(v) {
    f <- function(beta) f_one(beta, v)
    est <- f(beta_hat)
    grad <- num_grad(f, beta_hat)
    se <- sqrt(drop(t(grad) %*% V %*% grad))
    tibble(variable = v, estimate = est, std_error = se,
           p_value = 2 * pnorm(abs(est / se), lower.tail = FALSE))
  }))
}

# ============================================================
# Реплицируем таблицу 1
# ============================================================
table1 <- survey %>%
  mutate(
    Treatment = case_when(
      treatment == "control" ~ "Control",
      treatment == "original" ~ "Original",
      treatment == "nochat" ~ "NoChat",
      treatment == "nohelp" ~ "NoHelp",
      treatment == "random within" ~ "RandomWithin",
      treatment %in% c("random btw same", "random btw other") ~ "RandomBetween",
      TRUE ~ treatment
    ),
    `Group assignment` = case_when(
      Treatment == "Control" ~ "N/A",
      Treatment %in% c("Original", "NoChat", "NoHelp") ~ "Painting",
      TRUE ~ "Random"
    ),
    Chat = case_when(Treatment %in% c("Original", "RandomWithin", "RandomBetween") ~ "Yes", TRUE ~ "No"),
    `Other-Other` = case_when(Treatment %in% c("Original", "NoChat", "RandomWithin", "RandomBetween") ~ "Yes", TRUE ~ "No"),
    `Within/Between` = case_when(
      Treatment == "Control" ~ "N/A",
      Treatment == "RandomBetween" ~ "Between",
      TRUE ~ "Within"
    )
  ) %>%
  group_by(Treatment, `Group assignment`, Chat, `Other-Other`, `Within/Between`) %>%
  summarise(`No. sessions` = n_distinct(date), `No. subjects (A)` = n(), .groups = "drop") %>%
  arrange(match(Treatment, c("Control", "Original", "NoChat", "NoHelp", "RandomWithin", "RandomBetween")))

cat("\nTable 1 — Features of Experimental Sessions\n")
print(table1)

# ============================================================
# Реплицируем рисунок 1
# ============================================================
fig1_data <- behavior %>% filter(stage == 2, treatment == "original")

get_scenario_means <- function(data, scenario_number, label_a, label_b) {
  a_vars <- paste0("r", 1:5, "s", scenario_number, "_giveA")
  b_vars <- paste0("r", 1:5, "s", scenario_number, "_giveB")
  tibble(
    round = rep(1:5, 2),
    tokens = c(sapply(a_vars, function(v) mean(data[[v]], na.rm = TRUE)),
               sapply(b_vars, function(v) mean(data[[v]], na.rm = TRUE))),
    recipient = rep(c(label_a, label_b), each = 5)
  )
}

plot_fig1_panel <- function(df) {
  ggplot(df, aes(x = round, y = tokens, shape = recipient)) +
    geom_point(size = 3) +
    scale_x_continuous(limits = c(0, 5), breaks = 0:5) +
    scale_y_continuous(limits = c(0, 350), breaks = seq(0, 350, 50)) +
    labs(x = "Round", y = "Tokens", shape = NULL) +
    theme_bw() +
    theme(legend.position = "top", legend.background = element_rect(color = "black"), panel.grid.minor = element_blank())
}

fig1_s1 <- get_scenario_means(fig1_data, 1, "Ingroup A", "Ingroup B")
fig1_s2 <- get_scenario_means(fig1_data, 2, "Outgroup A", "Outgroup B")
fig1_s3 <- get_scenario_means(fig1_data, 3, "Ingroup", "Outgroup")

figure1 <- (plot_fig1_panel(fig1_s1) | plot_fig1_panel(fig1_s2)) / plot_fig1_panel(fig1_s3) +
  plot_annotation(title = "Figure 1. Other-Other Allocations in the Original Treatment")

ggsave(file.path(output_dir, "figure1_other_other_allocations.png"), figure1, width = 10, height = 8, dpi = 300)
cat("\nFigure 1 saved to outputs/figure1_other_other_allocations.png\n")

# ============================================================
# Реплицируем таблицу 2
# ============================================================
dist_control <- behavior %>%
  filter(stage == 3, treatment == "control", myrole == 2) %>%
  mutate(
    r1 = as.integer(payoffB_Bact1 > payoffA_Bact1),
    s1 = as.integer(payoffB_Bact1 < payoffA_Bact1),
    r2 = as.integer(payoffB_Bact2 > payoffA_Bact2),
    s2 = as.integer(payoffB_Bact2 < payoffA_Bact2),
    left = as.integer(actforsame == 1),
    x0 = payoffB_Bact1 - payoffB_Bact2,
    x1 = r1 * payoffA_Bact1 - r2 * payoffA_Bact2 + r2 * payoffB_Bact2 - r1 * payoffB_Bact1,
    x2 = s1 * payoffA_Bact1 - s2 * payoffA_Bact2 + s2 * payoffB_Bact2 - s1 * payoffB_Bact1
  ) %>%
  filter(!is.na(left), !is.na(x0), !is.na(x1), !is.na(x2))

m_control <- glm(left ~ x1 + x2 + x0 - 1, data = dist_control, family = binomial(link = "logit"))

table2_control <- bind_rows(
  ratio_se(m_control, "x1", "x0") %>% mutate(parameter = "rho"),
  ratio_se(m_control, "x2", "x0") %>% mutate(parameter = "sigma")
) %>% dplyr::select(parameter, estimate, std_error)

dist_original_wide <- behavior %>%
  filter(stage == 3, treatment == "original", myrole == 2) %>%
  mutate(
    r1 = as.integer(payoffB_Bact1 > payoffA_Bact1),
    s1 = as.integer(payoffB_Bact1 < payoffA_Bact1),
    r2 = as.integer(payoffB_Bact2 > payoffA_Bact2),
    s2 = as.integer(payoffB_Bact2 < payoffA_Bact2),
    x0 = payoffB_Bact1 - payoffB_Bact2,
    x1 = r1 * payoffA_Bact1 - r2 * payoffA_Bact2 + r2 * payoffB_Bact2 - r1 * payoffB_Bact1,
    x2 = s1 * payoffA_Bact1 - s2 * payoffA_Bact2 + s2 * payoffB_Bact2 - s1 * payoffB_Bact1
  )

dist_original <- bind_rows(
  dist_original_wide %>% transmute(act = actforsame, ingr = 1, x0, x1, x2),
  dist_original_wide %>% transmute(act = actforother, ingr = 0, x0, x1, x2)
) %>%
  mutate(left = as.integer(act == 1), ingr_x1 = ingr * x1, ingr_x2 = ingr * x2) %>%
  filter(!is.na(left), !is.na(x0), !is.na(x1), !is.na(x2))

m_original <- glm(left ~ x1 + x2 + ingr_x1 + ingr_x2 + x0 - 1, data = dist_original, family = binomial(link = "logit"))

table2_original <- bind_rows(
  ratio_se(m_original, "x1", "x0") %>% mutate(parameter = "rho_o"),
  ratio_se(m_original, "x2", "x0") %>% mutate(parameter = "sigma_o"),
  ratio_se(m_original, "ingr_x1", "x1") %>% mutate(parameter = "a"),
  ratio_se(m_original, "ingr_x2", "x2") %>% mutate(parameter = "b")
) %>% dplyr::select(parameter, estimate, std_error)

rho_o <- table2_original %>% filter(parameter == "rho_o") %>% pull(estimate)
sigma_o <- table2_original %>% filter(parameter == "sigma_o") %>% pull(estimate)
a <- table2_original %>% filter(parameter == "a") %>% pull(estimate)
b <- table2_original %>% filter(parameter == "b") %>% pull(estimate)

table2 <- tibble(
  Panel = c("A: Control", "A: Control", "B: Treatment", "B: Treatment", "B: Treatment", "B: Treatment", "B: Treatment", "B: Treatment"),
  Parameter = c("rho", "sigma", "rho_o", "sigma_o", "rho_o(1+a)", "sigma_o(1+b)", "a", "b"),
  Estimate = round(c(
    table2_control %>% filter(parameter == "rho") %>% pull(estimate),
    table2_control %>% filter(parameter == "sigma") %>% pull(estimate),
    rho_o, sigma_o, rho_o * (1 + a), sigma_o * (1 + b), a, b
  ), 3)
)

cat("\nTable 2 — Distribution Preferences: Maximum Likelihood Estimates\n")
print(table2)

# ============================================================
# Реплицируем таблицу 3
# ============================================================
positive_games <- c("Resp 5a", "Resp 1a", "Resp 2a", "Resp 3", "Resp 4", "Resp 8", "Resp 9")
pos_base <- behavior %>%
  filter(stage == 3, treatment %in% c("original", "control"), game %in% positive_games, myrole == 2) %>%
  mutate(
    sess_subj = paste(date, subject, sep = "_"),
    reward_ingr = case_when(actforsame == 2 ~ 1, actforsame == 1 ~ 0, TRUE ~ NA_real_),
    reward_outgr = case_when(actforother == 2 ~ 1, actforother == 1 ~ 0, TRUE ~ NA_real_),
    cost = (payoffB_Bact1 - payoffB_Bact2) / 100,
    benefitA = (payoffA_Bact2 - payoffA_Bact1) / 100,
    Bbehind = (payoffA_Bact2 - payoffB_Bact2) / 100
  )

pos_control <- pos_base %>% filter(treatment == "control") %>% transmute(sess_subj, reward = reward_ingr, cost, benefitA, Bbehind) %>% filter(!is.na(reward))
pos_original <- bind_rows(
  pos_base %>% filter(treatment == "original") %>% transmute(sess_subj, reward = reward_ingr, ingr = 1, cost, benefitA, Bbehind),
  pos_base %>% filter(treatment == "original") %>% transmute(sess_subj, reward = reward_outgr, ingr = 0, cost, benefitA, Bbehind)
) %>% filter(!is.na(reward))
pos_original_int <- pos_original %>% mutate(cost_ingr = cost * ingr, benefitA_ingr = benefitA * ingr, Bbehind_ingr = Bbehind * ingr)

m_pos_control <- glm(reward ~ cost + benefitA + Bbehind, data = pos_control, family = binomial(link = "logit"))
m_pos_original <- glm(reward ~ ingr + cost + benefitA + Bbehind, data = pos_original, family = binomial(link = "logit"))
m_pos_original_int <- glm(reward ~ ingr + cost + benefitA + Bbehind + cost_ingr + benefitA_ingr + Bbehind_ingr, data = pos_original_int, family = binomial(link = "logit"))

negative_games <- c("Resp 2b", "Resp 10", "Resp 11", "Resp 1b", "Resp 6", "Resp 7", "Resp 12", "Resp 13a", "Resp 13b", "Resp 13c", "Resp 13d")
punish_left_games <- c("Resp 2b", "Resp 1b", "Resp 6", "Resp 7")
punish_right_games <- c("Resp 10", "Resp 11", "Resp 12", "Resp 13a", "Resp 13b", "Resp 13c", "Resp 13d")

neg_base <- behavior %>%
  filter(stage == 3, treatment %in% c("original", "control"), game %in% negative_games, myrole == 2) %>%
  mutate(
    sess_subj = paste(date, subject, sep = "_"),
    punish_ingr = case_when(
      game %in% punish_left_games & actforsame == 1 ~ 1,
      game %in% punish_left_games & actforsame == 2 ~ 0,
      game %in% punish_right_games & actforsame == 2 ~ 1,
      game %in% punish_right_games & actforsame == 1 ~ 0,
      TRUE ~ NA_real_
    ),
    punish_outgr = case_when(
      game %in% punish_left_games & actforother == 1 ~ 1,
      game %in% punish_left_games & actforother == 2 ~ 0,
      game %in% punish_right_games & actforother == 2 ~ 1,
      game %in% punish_right_games & actforother == 1 ~ 0,
      TRUE ~ NA_real_
    ),
    cost = case_when(game %in% punish_left_games ~ (payoffB_Bact2 - payoffB_Bact1) / 100, game %in% punish_right_games ~ (payoffB_Bact1 - payoffB_Bact2) / 100),
    damageA = case_when(game %in% punish_left_games ~ (payoffA_Bact2 - payoffA_Bact1) / 100, game %in% punish_right_games ~ (payoffA_Bact1 - payoffA_Bact2) / 100),
    Bahead = case_when(game %in% punish_left_games ~ (payoffB_Bact1 - payoffA_Bact1) / 100, game %in% punish_right_games ~ (payoffB_Bact2 - payoffA_Bact2) / 100)
  )

neg_control <- neg_base %>% filter(treatment == "control") %>% transmute(sess_subj, punish = punish_ingr, cost, damageA, Bahead) %>% filter(!is.na(punish))
neg_original <- bind_rows(
  neg_base %>% filter(treatment == "original") %>% transmute(sess_subj, punish = punish_ingr, ingr = 1, cost, damageA, Bahead),
  neg_base %>% filter(treatment == "original") %>% transmute(sess_subj, punish = punish_outgr, ingr = 0, cost, damageA, Bahead)
) %>% filter(!is.na(punish))
neg_original_int <- neg_original %>% mutate(cost_ingr = cost * ingr, damageA_ingr = damageA * ingr, Bahead_ingr = Bahead * ingr)

m_neg_control <- glm(punish ~ cost + damageA + Bahead, data = neg_control, family = binomial(link = "logit"))
m_neg_original <- glm(punish ~ ingr + cost + damageA + Bahead, data = neg_original, family = binomial(link = "logit"))
m_neg_original_int <- glm(punish ~ ingr + cost + damageA + Bahead + cost_ingr + damageA_ingr + Bahead_ingr, data = neg_original_int, family = binomial(link = "logit"))

table3_raw <- bind_rows(
  logit_me_at_means(m_pos_control, pos_control, c("cost", "benefitA", "Bbehind"), "sess_subj") %>% mutate(panel = "A: Positive reciprocity", column = "Control"),
  logit_me_at_means(m_pos_original, pos_original, c("ingr", "cost", "benefitA", "Bbehind"), "sess_subj", dummy_vars = "ingr") %>% mutate(panel = "A: Positive reciprocity", column = "Treatment"),
  logit_me_interaction_table3(m_pos_original_int, pos_original_int, "sess_subj", "positive") %>% mutate(panel = "A: Positive reciprocity", column = "Treatment + interactions"),
  logit_me_at_means(m_neg_control, neg_control, c("cost", "damageA", "Bahead"), "sess_subj") %>% mutate(panel = "B: Negative reciprocity", column = "Control"),
  logit_me_at_means(m_neg_original, neg_original, c("ingr", "cost", "damageA", "Bahead"), "sess_subj", dummy_vars = "ingr") %>% mutate(panel = "B: Negative reciprocity", column = "Treatment"),
  logit_me_interaction_table3(m_neg_original_int, neg_original_int, "sess_subj", "negative") %>% mutate(panel = "B: Negative reciprocity", column = "Treatment + interactions")
)

table3 <- table3_raw %>%
  mutate(value = paste0(round(estimate, 3), " (", round(std_error, 3), ")", stars(p_value))) %>%
  dplyr::select(panel, variable, column, value) %>%
  pivot_wider(names_from = column, values_from = value)

cat("\nTable 3 — Logit Regression: Determinants of Reciprocity\n")
print(table3)

# ============================================================
# Реплицируем таблицу 4
# ============================================================
t4 <- behavior %>%
  filter(stage == 3, treatment %in% c("control", "original")) %>%
  filter(!(myrole == 1 & game %in% c("Dict 1", "Dict 2", "Dict 3", "Dict 4", "Dict 5"))) %>%
  filter(!game %in% c("Dict 5", "Resp 5a", "Resp 5b")) %>%
  filter(!(game == "Resp 9" & myrole == 2)) %>%
  mutate(
    swmax_act = NA_real_,
    swmax_act = if_else(myrole == 1 & game %in% c("Resp 1a", "Resp 2a", "Resp 3", "Resp 4", "Resp 8", "Resp 9") & is.na(swmax_act), 2, swmax_act),
    swmax_act = if_else(myrole == 1 & game %in% c("Resp 1b", "Resp 6", "Resp 7", "Resp 2b", "Resp 10", "Resp 11", "Resp 12", "Resp 13a", "Resp 13b", "Resp 13c", "Resp 13d") & is.na(swmax_act), 1, swmax_act),
    swmax_act = if_else(myrole == 2 & game %in% c("Dict 1", "Dict 2", "Dict 3", "Dict 4", "Resp 1a", "Resp 1b", "Resp 6", "Resp 7", "Resp 2a", "Resp 2b", "Resp 3", "Resp 4", "Resp 8") & is.na(swmax_act), 2, swmax_act),
    swmax_act = if_else(myrole == 2 & game %in% c("Resp 10", "Resp 11", "Resp 12", "Resp 13a", "Resp 13b", "Resp 13c", "Resp 13d") & is.na(swmax_act), 1, swmax_act),
    ingr_swm = case_when(actforsame == swmax_act ~ 1, actforsame != swmax_act & actforsame != 0 ~ 0, TRUE ~ NA_real_),
    outgr_swm = case_when(treatment == "original" & actforother == swmax_act ~ 1, treatment == "original" & actforother != swmax_act & actforother != 0 ~ 0, TRUE ~ NA_real_),
    sess_subj = paste(date, subject, sep = "_"),
    original = as.integer(treatment == "original"),
    role = if_else(myrole == 1, "Player A", "Player B")
  )

props4 <- tibble(
  role = c("Player A", "Player B", "Overall"),
  Ingroup = c(mean(t4$ingr_swm[t4$treatment == "original" & t4$myrole == 1], na.rm = TRUE), mean(t4$ingr_swm[t4$treatment == "original" & t4$myrole == 2], na.rm = TRUE), mean(t4$ingr_swm[t4$treatment == "original"], na.rm = TRUE)),
  n_ingroup = c(sum(!is.na(t4$ingr_swm[t4$treatment == "original" & t4$myrole == 1])), sum(!is.na(t4$ingr_swm[t4$treatment == "original" & t4$myrole == 2])), sum(!is.na(t4$ingr_swm[t4$treatment == "original"]))),
  Outgroup = c(mean(t4$outgr_swm[t4$treatment == "original" & t4$myrole == 1], na.rm = TRUE), mean(t4$outgr_swm[t4$treatment == "original" & t4$myrole == 2], na.rm = TRUE), mean(t4$outgr_swm[t4$treatment == "original"], na.rm = TRUE)),
  n_outgroup = c(sum(!is.na(t4$outgr_swm[t4$treatment == "original" & t4$myrole == 1])), sum(!is.na(t4$outgr_swm[t4$treatment == "original" & t4$myrole == 2])), sum(!is.na(t4$outgr_swm[t4$treatment == "original"]))),
  Control = c(mean(t4$ingr_swm[t4$treatment == "control" & t4$myrole == 1], na.rm = TRUE), mean(t4$ingr_swm[t4$treatment == "control" & t4$myrole == 2], na.rm = TRUE), mean(t4$ingr_swm[t4$treatment == "control"], na.rm = TRUE)),
  n_control = c(sum(!is.na(t4$ingr_swm[t4$treatment == "control" & t4$myrole == 1])), sum(!is.na(t4$ingr_swm[t4$treatment == "control" & t4$myrole == 2])), sum(!is.na(t4$ingr_swm[t4$treatment == "control"])))
)

get_table4_pvals <- function(role_name = NULL) {
  d <- t4
  if (!is.null(role_name)) d <- d %>% filter(role == role_name)
  d_io <- bind_rows(
    d %>% filter(treatment == "original") %>% transmute(sess_subj, swm = ingr_swm, ingr = 1),
    d %>% filter(treatment == "original") %>% transmute(sess_subj, swm = outgr_swm, ingr = 0)
  ) %>% filter(!is.na(swm))
  d_ic <- d %>% filter(!is.na(ingr_swm))
  d_co <- d %>% mutate(outgr_for_test = if_else(treatment == "control", ingr_swm, outgr_swm)) %>% filter(!is.na(outgr_for_test))
  tibble(
    role = ifelse(is.null(role_name), "Overall", role_name),
    `Ingroup > Outgroup` = cluster_reg_p_one_sided(d_io, swm ~ ingr, "sess_subj", "ingr", "greater"),
    `Ingroup > Control` = cluster_reg_p_one_sided(d_ic, ingr_swm ~ original, "sess_subj", "original", "greater"),
    `Control > Outgroup` = cluster_reg_p_one_sided(d_co, outgr_for_test ~ original, "sess_subj", "original", "less")
  )
}

pvals4 <- bind_rows(get_table4_pvals("Player A"), get_table4_pvals("Player B"), get_table4_pvals(NULL))

table4 <- props4 %>%
  left_join(pvals4, by = "role") %>%
  mutate(
    Ingroup = paste0(round(Ingroup, 3), " [", n_ingroup, "]"),
    Outgroup = paste0(round(Outgroup, 3), " [", n_outgroup, "]"),
    Control = paste0(round(Control, 3), " [", n_control, "]"),
    `Ingroup > Outgroup` = round(`Ingroup > Outgroup`, 3),
    `Ingroup > Control` = round(`Ingroup > Control`, 3),
    `Control > Outgroup` = round(`Control > Outgroup`, 3)
  ) %>%
  dplyr::select(role, Ingroup, Outgroup, Control, `Ingroup > Outgroup`, `Ingroup > Control`, `Control > Outgroup`)

cat("\nTable 4 — Proportion of SWM Decisions and the Effects of Social Identity\n")
print(table4)

# ============================================================
# Реплицируем таблицу 5
# ============================================================
session_map <- tibble(
  date = c("050316PQ", "050318OT", "050319OR", "050325PO", "050326P3", "050401QD", "050722O6", "050801LR", "050801NP", "050127R4", "050202PR", "050203QK", "050207OP", "050209Q5", "050210PP", "050211LN", "050216PO", "050217PL", "050219PM", "050720LQ", "050720NP", "050722M3", "050729LO", "050729NK"),
  sess = 1:24
)

game_map <- tibble(
  game = c("Dict 1", "Dict 2", "Dict 3", "Dict 4", "Dict 5", "Resp 1a", "Resp 1b", "Resp 6", "Resp 7", "Resp 2a", "Resp 2b", "Resp 3", "Resp 4", "Resp 5a", "Resp 5b", "Resp 8", "Resp 9", "Resp 10", "Resp 11", "Resp 12", "Resp 13a", "Resp 13b", "Resp 13c", "Resp 13d"),
  game_code = 1:24
)

base <- behavior %>%
  filter(stage == 3, treatment %in% c("control", "original")) %>%
  left_join(session_map, by = "date") %>%
  left_join(game_map, by = "game") %>%
  mutate(sess_subj = paste(date, subject, sep = "_"), original = as.integer(treatment == "original"), role = if_else(myrole == 1, "Player A", "Player B"))

fake_ids <- tibble(fakeopp_id = 1:16)

expected_pairs <- base %>%
  dplyr::select(treatment, date, sess, round, subject, mytype, myrole, actforsame, actforother, game, game_code, sess_subj, payoffA_Aout, payoffB_Aout, payoffA_Bact1, payoffB_Bact1, payoffA_Bact2, payoffB_Bact2) %>%
  tidyr::crossing(fake_ids) %>%
  filter(subject != fakeopp_id) %>%
  filter(!(date == "050127R4" & fakeopp_id == 16)) %>%
  filter(!(date == "050316PQ" & fakeopp_id %in% c(15, 16))) %>%
  filter(!(date == "050326P3" & fakeopp_id >= 13)) %>%
  filter(!(date == "050401QD" & fakeopp_id >= 15)) %>%
  filter(!(date == "050722O6" & fakeopp_id >= 15)) %>%
  filter(!(date == "050207OP" & fakeopp_id %in% c(1, 10))) %>%
  filter(!(date == "050316PQ" & fakeopp_id == 3))

opp_lookup <- base %>%
  dplyr::select(date, sess, game_code, fakeopp_id = subject, fakeopp_type = mytype, fakeopp_role = myrole, fakeopp_actforsame = actforsame, fakeopp_actforother = actforother)

expected_pairs <- expected_pairs %>%
  left_join(opp_lookup, by = c("date", "sess", "game_code", "fakeopp_id")) %>%
  filter(myrole != fakeopp_role) %>%
  mutate(
    actforsame = if_else(is.na(actforsame) & myrole == 1, 0, actforsame),
    actforother = if_else(is.na(actforother) & myrole == 1 & treatment == "original", 0, actforother),
    fakeopp_actforsame = if_else(is.na(fakeopp_actforsame) & fakeopp_role == 1, 0, fakeopp_actforsame),
    fakeopp_actforother = if_else(is.na(fakeopp_actforother) & fakeopp_role == 1 & treatment == "original", 0, fakeopp_actforother),
    fake_sametype = case_when(treatment == "original" & mytype == fakeopp_type ~ 1, treatment == "original" & mytype != fakeopp_type ~ 0, TRUE ~ NA_real_),
    fake_myact = case_when(treatment == "original" & fake_sametype == 1 ~ actforsame, treatment == "original" & fake_sametype == 0 ~ actforother, treatment == "control" ~ actforsame),
    fakeopp_act = case_when(treatment == "original" & fake_sametype == 1 ~ fakeopp_actforsame, treatment == "original" & fake_sametype == 0 ~ fakeopp_actforother, treatment == "control" ~ fakeopp_actforsame),
    fake_asact = if_else(myrole == 1, fake_myact, fakeopp_act),
    fake_bsact = if_else(myrole == 2, fake_myact, fakeopp_act),
    case_num = 3 * fake_asact + fake_bsact,
    fake_aspayoff = case_when(case_num == 1 ~ payoffA_Bact1, case_num == 2 ~ payoffA_Bact2, case_num == 4 ~ payoffA_Aout, case_num == 5 ~ payoffA_Aout, case_num == 7 ~ payoffA_Bact1, case_num == 8 ~ payoffA_Bact2),
    fake_bspayoff = case_when(case_num == 1 ~ payoffB_Bact1, case_num == 2 ~ payoffB_Bact2, case_num == 4 ~ payoffB_Aout, case_num == 5 ~ payoffB_Aout, case_num == 7 ~ payoffB_Bact1, case_num == 8 ~ payoffB_Bact2),
    fake_mypayoff = if_else(myrole == 1, fake_aspayoff, fake_bspayoff)
  )

expected_long <- expected_pairs %>%
  group_by(treatment, date, game, subject, fake_sametype) %>%
  summarise(fake_mypayoff = mean(fake_mypayoff, na.rm = TRUE), myrole = mean(myrole, na.rm = TRUE), sess_subj = first(sess_subj), .groups = "drop") %>%
  mutate(role = if_else(myrole == 1, "Player A", "Player B"),
         match_type = case_when(treatment == "original" & fake_sametype == 1 ~ "Ingroup", treatment == "original" & fake_sametype == 0 ~ "Outgroup", treatment == "control" ~ "Control"),
         earnings = fake_mypayoff) %>%
  filter(!is.na(match_type), !is.na(earnings))

actual_long <- bind_rows(
  base %>% filter(treatment == "original", sametype == 1) %>% transmute(sess_subj, role, match_type = "Ingroup", earnings = mypayoff),
  base %>% filter(treatment == "original", sametype == 0) %>% transmute(sess_subj, role, match_type = "Outgroup", earnings = mypayoff),
  base %>% filter(treatment == "control") %>% transmute(sess_subj, role, match_type = "Control", earnings = mypayoff)
) %>% filter(!is.na(earnings))

get_table5 <- function(data, panel_name) {
  means_role <- data %>% group_by(role, match_type) %>% summarise(n = n(), earnings = mean(earnings), .groups = "drop")
  means_overall <- data %>% group_by(match_type) %>% summarise(role = "Overall", n = n(), earnings = mean(earnings), .groups = "drop") %>% dplyr::select(role, match_type, n, earnings)
  means <- bind_rows(means_role, means_overall)

  get_p <- function(role_name = NULL) {
    d <- data
    if (!is.null(role_name)) d <- d %>% filter(role == role_name)
    d_io <- d %>% filter(match_type %in% c("Ingroup", "Outgroup")) %>% mutate(ingroup = as.integer(match_type == "Ingroup"))
    d_ic <- d %>% filter(match_type %in% c("Ingroup", "Control")) %>% mutate(ingroup = as.integer(match_type == "Ingroup"))
    d_co <- d %>% filter(match_type %in% c("Control", "Outgroup")) %>% mutate(control = as.integer(match_type == "Control"))
    tibble(
      role = ifelse(is.null(role_name), "Overall", role_name),
      `Ingroup > Outgroup` = cluster_reg_p_one_sided(d_io, earnings ~ ingroup, "sess_subj", "ingroup", "greater"),
      `Ingroup > Control` = cluster_reg_p_one_sided(d_ic, earnings ~ ingroup, "sess_subj", "ingroup", "greater"),
      `Control > Outgroup` = cluster_reg_p_one_sided(d_co, earnings ~ control, "sess_subj", "control", "greater")
    )
  }

  pvals <- bind_rows(get_p("Player A"), get_p("Player B"), get_p(NULL))
  means %>%
    mutate(value = format_mean_n(earnings, n)) %>%
    dplyr::select(role, match_type, value) %>%
    pivot_wider(names_from = match_type, values_from = value) %>%
    left_join(pvals, by = "role") %>%
    mutate(panel = panel_name,
           `Ingroup > Outgroup` = round(`Ingroup > Outgroup`, 3),
           `Ingroup > Control` = round(`Ingroup > Control`, 3),
           `Control > Outgroup` = round(`Control > Outgroup`, 3)) %>%
    arrange(factor(role, levels = c("Player A", "Player B", "Overall"))) %>%
    dplyr::select(panel, role, Ingroup, Outgroup, Control, `Ingroup > Outgroup`, `Ingroup > Control`, `Control > Outgroup`)
}

table5 <- bind_rows(get_table5(expected_long, "Expected earnings"), get_table5(actual_long, "Actual earnings"))
cat("\nTable 5 — Effects of Social Identity on Expected and Actual Earnings\n")
print(table5)

# ============================================================
# Реплицируем таблицу 6
# ============================================================
table6_subject <- behavior %>%
  filter(stage == 3, treatment != "control", !treatment %in% c("random btw same", "random btw other")) %>%
  filter(!(myrole == 1 & game %in% c("Dict 1", "Dict 2", "Dict 3", "Dict 4", "Dict 5"))) %>%
  mutate(diff = as.integer(actforsame != actforother)) %>%
  group_by(treatment, date, myrole, subject) %>%
  summarise(diff_sum = sum(diff, na.rm = TRUE), .groups = "drop") %>%
  mutate(
    subj_diff = as.integer(diff_sum > 0),
    Role = if_else(myrole == 1, "Role A", "Role B"),
    Treatment = case_when(treatment == "original" ~ "Original", treatment == "nochat" ~ "NoChat", treatment == "nohelp" ~ "NoHelp", treatment == "randomwithin" ~ "RandomWithin")
  )

table6_top <- table6_subject %>%
  group_by(Treatment, Role) %>%
  summarise(Proportion = round(mean(subj_diff), 2), .groups = "drop") %>%
  pivot_wider(names_from = Treatment, values_from = Proportion) %>%
  dplyr::select(Role, Original, NoChat, NoHelp, RandomWithin)

stata_prtest_pooled <- function(data, treat_a, treat_b, role_name) {
  s <- data %>% filter(Treatment %in% c(treat_a, treat_b), Role == role_name) %>%
    group_by(Treatment) %>% summarise(x = sum(subj_diff), n = n(), p = mean(subj_diff), .groups = "drop")
  a <- s %>% filter(Treatment == treat_a)
  b <- s %>% filter(Treatment == treat_b)
  p_pool <- (a$x + b$x) / (a$n + b$n)
  se <- sqrt(p_pool * (1 - p_pool) * (1 / a$n + 1 / b$n))
  2 * pnorm(abs((a$p - b$p) / se), lower.tail = FALSE)
}

comparisons <- tibble(
  Comparison = c("Original vs. RandomWithin", "Original vs. NoChat", "NoChat vs. NoHelp", "Original vs. NoHelp"),
  treat_a = c("Original", "Original", "NoChat", "Original"),
  treat_b = c("RandomWithin", "NoChat", "NoHelp", "NoHelp")
)

table6_bottom <- comparisons %>%
  rowwise() %>%
  mutate(`Role A` = round(stata_prtest_pooled(table6_subject, treat_a, treat_b, "Role A"), 2),
         `Role B` = round(stata_prtest_pooled(table6_subject, treat_a, treat_b, "Role B"), 2)) %>%
  ungroup() %>%
  dplyr::select(Comparison, `Role A`, `Role B`)

table6 <- bind_rows(
  table6_top %>%
    rename(Comparison = Role),
  table6_bottom
)

cat("\nTable 6 — Proportion of Participants Who Differentiate Between Ingroup and Outgroup Matches\n")
print(table6)

# ============================================================
# Реплицируем таблицу 7
# ============================================================
table7_data <- survey %>%
  filter(treatment != "control") %>%
  mutate(
    paintings = case_when(treatment %in% c("original", "nochat", "nohelp") ~ 1, treatment %in% c("random within", "random btw same", "random btw other") ~ 0),
    chat = case_when(treatment %in% c("original", "random within", "random btw same", "random btw other") ~ 1, treatment %in% c("nochat", "nohelp") ~ 0),
    oo = case_when(treatment %in% c("original", "nochat", "random within", "random btw same", "random btw other") ~ 1, treatment == "nohelp" ~ 0),
    within_subj = case_when(treatment %in% c("original", "random within", "nochat", "nohelp") ~ 1, treatment %in% c("random btw same", "random btw other") ~ 0)
  ) %>%
  filter(!is.na(attach_to_gr), !is.na(paintings), !is.na(chat), !is.na(oo), !is.na(within_subj))

m7_ols <- lm(attach_to_gr ~ paintings + chat + oo + within_subj, data = table7_data)
ols_res <- lmtest::coeftest(m7_ols, vcov. = sandwich::vcovCL(m7_ols, cluster = table7_data$date, type = "HC1"))

m7_ologit <- MASS::polr(as.factor(attach_to_gr) ~ paintings + chat + oo + within_subj, data = table7_data, method = "logistic", Hess = TRUE)
ologit_res <- lmtest::coeftest(m7_ologit, vcov. = sandwich::vcovCL(m7_ologit, cluster = table7_data$date, type = "HC0"))

m7_ologit_null <- MASS::polr(as.factor(attach_to_gr) ~ 1, data = table7_data, method = "logistic", Hess = TRUE)

table7_ols <- tibble(model = "OLS", variable = rownames(ols_res), estimate = ols_res[, 1], std_error = ols_res[, 2], p_value = ols_res[, 4])
table7_ologit <- tibble(model = "Ordered logit", variable = rownames(ologit_res), estimate = ologit_res[, 1], std_error = ologit_res[, 2], p_value = ologit_res[, 4]) %>%
  filter(variable %in% c("paintings", "chat", "oo", "within_subj"))

table7 <- bind_rows(table7_ols, table7_ologit) %>%
  mutate(
    variable = recode(variable, "(Intercept)" = "Constant", "paintings" = "Paintings", "chat" = "Chat", "oo" = "Other-other allocation", "within_subj" = "Within-subject"),
    value = paste0(round(estimate, 3), " (", round(std_error, 3), ")", stars(p_value))
  ) %>%
  dplyr::select(variable, model, value) %>%
  pivot_wider(names_from = model, values_from = value)

table7_stats <- tibble(
  Statistic = c("Observations", "R2 / pseudo-R2"),
  OLS = c(nobs(m7_ols), round(summary(m7_ols)$adj.r.squared, 3)),
  `Ordered logit` = c(nobs(m7_ologit), round(1 - as.numeric(logLik(m7_ologit) / logLik(m7_ologit_null)), 3))
)

cat("\nTable 7 — Effects of Design Components on Self-Reported Group Attachment\n")
print(table7)
print(table7_stats)

# ============================================================
# Сохраняем полученные таблицы в эксель
# ============================================================
writexl::write_xlsx(
  list(
    "Table 1" = table1,
    "Table 2" = table2,
    "Table 3" = table3,
    "Table 4" = table4,
    "Table 5" = table5,
    "Table 6" = table6,
    "Table 7" = table7,
    "Table 7 stats" = table7_stats
  ),
  path = file.path(output_dir, "replication_tables.xlsx")
)