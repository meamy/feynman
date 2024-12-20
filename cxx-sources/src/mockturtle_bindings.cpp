#include <mockturtle/algorithms/cleanup.hpp>
#include <mockturtle/algorithms/xag_optimization.hpp>
#include <mockturtle/algorithms/xag_resub.hpp>
#include <mockturtle/algorithms/xag_resub_withDC.hpp>
#include <mockturtle/mockturtle.hpp>
#include <mockturtle/networks/xag.hpp>

#include <assert.h>
#include <stdint.h>

#include <deque>
#include <unordered_map>

constexpr static int32_t xag_wrap_t_magic = 0x9b131af7;
constexpr static int32_t xag_builder_wrap_t_magic = 0x9ec91078;
constexpr static int32_t xag_reader_wrap_t_magic = 0x62aa679e;

constexpr static int32_t xag_node_type_const_false = 0;
constexpr static int32_t xag_node_type_const_true = 1;
constexpr static int32_t xag_node_type_not = 2;
constexpr static int32_t xag_node_type_xor = 3;
constexpr static int32_t xag_node_type_and = 4;

struct xag_wrap_t {
  mockturtle::xag_network xag;
  int32_t magic;
};

struct xag_builder_wrap_t {
  mockturtle::xag_network xag;
  std::unordered_map<int32_t, mockturtle::xag_network::signal> nid_map;
  int32_t magic;
};

struct xag_ready_node_t {
  int32_t node_type;
  int32_t node_id;
  int32_t x_id;
  int32_t y_id;
};

struct xag_reader_wrap_t {
  mockturtle::xag_network xag;
  int32_t magic;

  std::deque<int32_t> pi_nids;
  std::deque<xag_ready_node_t> nodes;
  std::deque<int32_t> po_nids;
};

/*
foreach node n:
  xag_ready_node_t ready;
  foreach sig_in si:
    if si not in sig_map:
      if si complemented:
        infer_not(si)
    if si not in sig_map:
      incomplete_sig_map.add(n, si)
    else:
      if ready.x_id == -2:
        ready_xid = si
      else if ready.y_id == -2:
        ready_yid = si


*/

extern "C" {
xag_wrap_t *xag_alloc();
void xag_free(xag_wrap_t *xag_p);
void xag_optimize(xag_wrap_t *xag_p);
xag_builder_wrap_t *xag_builder_alloc(xag_wrap_t *xag_p);
void xag_builder_free(xag_builder_wrap_t *builder_p);
void xag_builder_create_pi(xag_builder_wrap_t *builder_p, int32_t node_id);
void xag_builder_create_const(xag_builder_wrap_t *builder_p, int32_t node_id,
                              bool value);
void xag_builder_create_not(xag_builder_wrap_t *builder_p, int32_t node_id,
                            int32_t x_id);
void xag_builder_create_xor(xag_builder_wrap_t *builder_p, int32_t node_id,
                            int32_t x_id, int32_t y_id);
void xag_builder_create_and(xag_builder_wrap_t *builder_p, int32_t node_id,
                            int32_t x_id, int32_t y_id);
void xag_builder_create_po(xag_builder_wrap_t *builder_p, int32_t node_id);
xag_reader_wrap_t *xag_reader_alloc(xag_wrap_t *xag_p);
void xag_reader_free(xag_reader_wrap_t *reader_p);
int32_t xag_reader_get_num_pis(xag_reader_wrap_t *reader_p);
int32_t xag_reader_get_num_nodes(xag_reader_wrap_t *reader_p);
int32_t xag_reader_get_num_pos(xag_reader_wrap_t *reader_p);
void xag_reader_reset_pis(xag_reader_wrap_t *reader_p);
int32_t xag_reader_read_next_pi(xag_reader_wrap_t *reader_p);
void xag_reader_reset_nodes(xag_reader_wrap_t *reader_p);
int32_t xag_reader_read_next_node(xag_reader_wrap_t *reader_p,
                                  int32_t node_data[3]);
void xag_reader_reset_pos(xag_reader_wrap_t *reader_p);
int32_t xag_reader_read_next_po(xag_reader_wrap_t *reader_p);
}

xag_wrap_t *xag_alloc() { return new xag_wrap_t{.magic = xag_wrap_t_magic}; }

void xag_free(xag_wrap_t *xag_p) {
  assert(xag_p);
  assert(xag_p->magic == xag_wrap_t_magic);

  xag_p->magic = 0;
  delete xag_p;
}

void xag_optimize(xag_wrap_t *xag_p) {
  using namespace mockturtle;

  assert(xag_p);
  assert(xag_p->magic == xag_wrap_t_magic);

  // xag_p->xag = exact_linear_resynthesis_optimization(xag_p->xag); // kaboom
  xag_p->xag = xag_constant_fanin_optimization(xag_p->xag);
  xag_p->xag = cleanup_dangling(xag_p->xag);

  xag_p->xag.foreach_node([&xag = xag_p->xag](auto n) {
    char type_c = xag.is_and(n)   ? 'A'
                  : xag.is_xor(n) ? 'X'
                  : xag.is_pi(n)  ? 'I'
                                  : '?';
    fprintf(stderr, "  X0 %c%d:", type_c, (int)n);
    xag.foreach_fanin(n, [](auto s) { fprintf(stderr, " %d", (int)s.data); });
    fprintf(stderr, "\n");
  });

  resubstitution_params ps{.max_divisors = 10000,
                           .max_inserts = 1000,
                           .verbose = true,
                           .use_dont_cares = true};

  using view_t = depth_view<fanout_view<xag_network>>;
  fanout_view<xag_network> fanout_view{xag_p->xag};
  view_t resub_view{fanout_view};
  // xag_resubstitution(resub_view, ps);
  resubstitution_minmc_withDC(resub_view, ps);

  resub_view.foreach_node([&xag = resub_view](auto n) {
    char type_c = xag.is_and(n)   ? 'A'
                  : xag.is_xor(n) ? 'X'
                  : xag.is_pi(n)  ? 'I'
                                  : '?';
    fprintf(stderr, "  V %c%d:", type_c, (int)n);
    xag.foreach_fanin(n, [](auto s) { fprintf(stderr, " %d", (int)s.data); });
    fprintf(stderr, "\n");
  });

  // xag_p->xag = exact_linear_resynthesis_optimization(xag_p->xag);
  xag_p->xag = cleanup_dangling(xag_p->xag);

  xag_p->xag.foreach_node([&xag = xag_p->xag](auto n) {
    char type_c = xag.is_and(n)   ? 'A'
                  : xag.is_xor(n) ? 'X'
                  : xag.is_pi(n)  ? 'I'
                                  : '?';
    fprintf(stderr, "  X1 %c%d:", type_c, (int)n);
    xag.foreach_fanin(n, [](auto s) { fprintf(stderr, " %d", (int)s.data); });
    fprintf(stderr, "\n");
  });
}

xag_builder_wrap_t *xag_builder_alloc(xag_wrap_t *xag_p) {
  assert(xag_p);
  assert(xag_p->magic == xag_wrap_t_magic);

  return new xag_builder_wrap_t{.xag = xag_p->xag,
                                .magic = xag_builder_wrap_t_magic};
}

void xag_builder_free(xag_builder_wrap_t *builder_p) {
  assert(builder_p);
  assert(builder_p->magic == xag_builder_wrap_t_magic);

  builder_p->magic = 0;
  delete builder_p;
}

void xag_builder_create_pi(xag_builder_wrap_t *builder_p, int32_t node_id) {
  assert(builder_p);
  assert(builder_p->magic == xag_builder_wrap_t_magic);
  assert(builder_p->nid_map.find(node_id) == builder_p->nid_map.end());

  builder_p->nid_map.emplace(node_id, builder_p->xag.create_pi());
}

void xag_builder_create_const(xag_builder_wrap_t *builder_p, int32_t node_id,
                              bool value) {
  assert(builder_p);
  assert(builder_p->magic == xag_builder_wrap_t_magic);
  assert(builder_p->nid_map.find(node_id) == builder_p->nid_map.end());

  builder_p->nid_map.emplace(node_id, builder_p->xag.get_constant(value));
}

void xag_builder_create_not(xag_builder_wrap_t *builder_p, int32_t node_id,
                            int32_t x_id) {
  assert(builder_p);
  assert(builder_p->magic == xag_builder_wrap_t_magic);
  assert(builder_p->nid_map.find(node_id) == builder_p->nid_map.end());
  assert(builder_p->nid_map.find(x_id) != builder_p->nid_map.end());

  auto x_sig = builder_p->nid_map.at(x_id);
  builder_p->nid_map.emplace(node_id, builder_p->xag.create_not(x_sig));
}

void xag_builder_create_xor(xag_builder_wrap_t *builder_p, int32_t node_id,
                            int32_t x_id, int32_t y_id) {
  assert(builder_p);
  assert(builder_p->magic == xag_builder_wrap_t_magic);
  assert(builder_p->nid_map.find(node_id) == builder_p->nid_map.end());
  assert(builder_p->nid_map.find(x_id) != builder_p->nid_map.end());
  assert(builder_p->nid_map.find(y_id) != builder_p->nid_map.end());

  auto x_sig = builder_p->nid_map.at(x_id);
  auto y_sig = builder_p->nid_map.at(y_id);
  builder_p->nid_map.emplace(node_id, builder_p->xag.create_xor(x_sig, y_sig));
}

void xag_builder_create_and(xag_builder_wrap_t *builder_p, int32_t node_id,
                            int32_t x_id, int32_t y_id) {
  assert(builder_p);
  assert(builder_p->magic == xag_builder_wrap_t_magic);
  assert(builder_p->nid_map.find(node_id) == builder_p->nid_map.end());
  assert(builder_p->nid_map.find(x_id) != builder_p->nid_map.end());
  assert(builder_p->nid_map.find(y_id) != builder_p->nid_map.end());

  auto x_sig = builder_p->nid_map.at(x_id);
  auto y_sig = builder_p->nid_map.at(y_id);
  builder_p->nid_map.emplace(node_id, builder_p->xag.create_and(x_sig, y_sig));
}

void xag_builder_create_po(xag_builder_wrap_t *builder_p, int32_t x_id) {
  assert(builder_p);
  assert(builder_p->magic == xag_builder_wrap_t_magic);
  assert(builder_p->nid_map.find(x_id) != builder_p->nid_map.end());

  auto x_sig = builder_p->nid_map.at(x_id);
  builder_p->xag.create_po(x_sig);
}

xag_reader_wrap_t *xag_reader_alloc(xag_wrap_t *xag_p) {
  using signal = mockturtle::xag_network::signal;
  using node = mockturtle::xag_network::node;

  assert(xag_p);
  assert(xag_p->magic == xag_wrap_t_magic);

  mockturtle::topo_view<mockturtle::xag_network> topo{xag_p->xag};

  std::unordered_map<signal, int32_t> sig_map;
  std::deque<int32_t> pi_nids;
  std::deque<xag_ready_node_t> nodes;
  std::deque<int32_t> po_nids;
  int32_t next_nid = 0;
  int32_t f_id = -1;
  int32_t t_id = -1;

  auto find_id_inferring_trivial = [&](signal s) {
    if (topo.is_constant(topo.get_node(s))) {
      if (topo.constant_value(topo.get_node(s)) == false) {
        if (f_id == -1) {
          f_id = next_nid++;
          nodes.emplace_back(
              xag_ready_node_t{.node_type = xag_node_type_const_false,
                               .node_id = f_id,
                               .x_id = -1,
                               .y_id = -1});
        }
        return f_id;
      } else {
        if (t_id == -1) {
          t_id = next_nid++;
          nodes.emplace_back(
              xag_ready_node_t{.node_type = xag_node_type_const_true,
                               .node_id = t_id,
                               .x_id = -1,
                               .y_id = -1});
        }
        return t_id;
      }
    } else {
      auto i = sig_map.find(s);
      if (i == sig_map.end()) {
        assert(topo.is_complemented(s));
        assert(sig_map.find(!s) != sig_map.end());
        int32_t nid = next_nid++;
        nodes.emplace_back(xag_ready_node_t{.node_type = xag_node_type_not,
                                            .node_id = nid,
                                            .x_id = sig_map.at(!s),
                                            .y_id = -1});
        sig_map.emplace(s, nid);
        return nid;
      } else {
        return i->second;
      }
    }
  };

  topo.foreach_pi([&](node n) {
    int32_t nid = next_nid++;
    signal s = topo.make_signal(n);
    assert(!topo.is_complemented(s));
    sig_map.emplace(s, nid);
    pi_nids.emplace_back(nid);
  });

  topo.foreach_gate([&](node n) {
    assert(topo.is_xor(n) || topo.is_and(n));
    int32_t x_id = -1;
    int32_t y_id = -1;
    topo.foreach_fanin(n, [&](signal fi_s) {
      int32_t fi_id = find_id_inferring_trivial(fi_s);
      assert(fi_id >= 0);
      if (x_id == -1) {
        x_id = fi_id;
      } else if (y_id == -1) {
        y_id = fi_id;
      } else {
        assert(!"nodes should have exactly two inputs");
      }
    });
    int32_t nid = next_nid++;
    assert(x_id >= 0 && y_id >= 0);
    int32_t node_type = -1;
    if (topo.is_xor(n)) {
      node_type = xag_node_type_xor;
    } else if (topo.is_and(n)) {
      node_type = xag_node_type_and;
    } else {
      assert(!"nodes should be either xor or and");
    }
    nodes.emplace_back(xag_ready_node_t{
        .node_type = node_type, .node_id = nid, .x_id = x_id, .y_id = y_id});
    sig_map.emplace(topo.make_signal(n), nid);
  });

  topo.foreach_po([&](auto n) {
    auto nid = find_id_inferring_trivial(n);
    po_nids.emplace_back(nid);
  });

  return new xag_reader_wrap_t{
      .xag = xag_p->xag,
      .magic = xag_reader_wrap_t_magic,
      .pi_nids = std::move(pi_nids),
      .nodes = std::move(nodes),
      .po_nids = std::move(po_nids),
  };
}

void xag_reader_free(xag_reader_wrap_t *reader_p) {
  assert(reader_p);
  assert(reader_p->magic == xag_reader_wrap_t_magic);

  reader_p->magic = 0;
  delete reader_p;
}

// Ptr XAGReaderWrap -> IO Int
int32_t xag_reader_get_num_pis(xag_reader_wrap_t *reader_p) {
  assert(reader_p);
  assert(reader_p->magic == xag_reader_wrap_t_magic);

  return reader_p->pi_nids.size();
}

// Ptr XAGReaderWrap -> IO Int
int32_t xag_reader_get_num_nodes(xag_reader_wrap_t *reader_p) {
  assert(reader_p);
  assert(reader_p->magic == xag_reader_wrap_t_magic);

  // an overapproximation because not isn't represented explicitly, so each
  // gate has an implicit inverted output, plus an implicit not for each PI
  return reader_p->nodes.size();
}

// Ptr XAGReaderWrap -> IO Int
int32_t xag_reader_get_num_pos(xag_reader_wrap_t *reader_p) {
  assert(reader_p);
  assert(reader_p->magic == xag_reader_wrap_t_magic);

  return reader_p->po_nids.size();
}

// Return is nodeID; nodeID < 0 means end
// Ptr XAGReaderWrap -> IO Int
int32_t xag_reader_read_next_pi(xag_reader_wrap_t *reader_p) {
  assert(reader_p);
  assert(reader_p->magic == xag_reader_wrap_t_magic);

  if (reader_p->pi_nids.empty()) {
    return -1;
  } else {
    int32_t nid = reader_p->pi_nids.front();
    reader_p->pi_nids.pop_front();
    return nid;
  }
}

// Param is array of 3 Int: type, xID, yID
// Return is nodeID; nodeID < 0 means end
// Ptr XAGReaderWrap -> Ptr Int -> IO Int
int32_t xag_reader_read_next_node(xag_reader_wrap_t *reader_p,
                                  int32_t node_data[3]) {
  assert(reader_p);
  assert(reader_p->magic == xag_reader_wrap_t_magic);

  if (reader_p->nodes.empty()) {
    return -1;
  } else {
    auto const &node = reader_p->nodes.front();
    node_data[0] = node.node_type;
    node_data[1] = node.x_id;
    node_data[2] = node.y_id;
    int32_t nid = node.node_id;
    reader_p->nodes.pop_front();
    return nid;
  }
}

// Return is nodeID; nodeID < 0 means end
// Ptr XAGReaderWrap -> IO Int
int32_t xag_reader_read_next_po(xag_reader_wrap_t *reader_p) {
  assert(reader_p);
  assert(reader_p->magic == xag_reader_wrap_t_magic);

  if (reader_p->po_nids.empty()) {
    return -1;
  } else {
    int32_t nid = reader_p->po_nids.front();
    reader_p->po_nids.pop_front();
    return nid;
  }
}
