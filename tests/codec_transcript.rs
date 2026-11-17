use ark_bls12_381::{Fr, G1Affine, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{One, Zero};
use hyperplonk_repair::{codec::*, transcript::*};
use num_bigint::BigInt;
use serde_json::Value;
use std::{collections::BTreeMap, str::FromStr};

fn vectors() -> Value {
    serde_json::from_str(include_str!("../testdata/codec_transcript.json")).unwrap()
}
fn bytes(value: &Value) -> Vec<u8> {
    hex::decode(value.as_str().unwrap()).unwrap()
}
fn context_value(value: &Value) -> ContextValue {
    match value["type"].as_str().unwrap() {
        "null" => ContextValue::Null,
        "bool" => ContextValue::Bool(value["value"].as_bool().unwrap()),
        "int" => ContextValue::Int(BigInt::from_str(value["value"].as_str().unwrap()).unwrap()),
        "bytes" => ContextValue::Bytes(bytes(&value["value"])),
        "text" => ContextValue::Text(value["value"].as_str().unwrap().into()),
        "list" => ContextValue::List(
            value["value"]
                .as_array()
                .unwrap()
                .iter()
                .map(context_value)
                .collect(),
        ),
        "map" => ContextValue::Map(
            value["value"]
                .as_object()
                .unwrap()
                .iter()
                .map(|(k, v)| (k.clone(), context_value(v)))
                .collect(),
        ),
        _ => panic!("bad fixture type"),
    }
}
fn domain(value: &Value) -> Domain {
    match value.as_str().unwrap() {
        "field" => Domain::Field,
        "nonzero" => Domain::Nonzero,
        "nonboolean" => Domain::Nonboolean,
        _ => panic!("bad domain"),
    }
}

#[test]
fn python_group_vectors_roundtrip_and_match_scalar_multiplication() {
    let v = vectors();
    for row in v["points"].as_array().unwrap() {
        let scalar = Fr::from_str(row["scalar"].as_str().unwrap()).unwrap();
        let g1 = g1_from_bytes(&bytes(&row["g1"])).unwrap();
        let g2 = g2_from_bytes(&bytes(&row["g2"])).unwrap();
        assert_eq!(g1, (G1Affine::generator() * scalar).into_affine());
        assert_eq!(g2, (G2Affine::generator() * scalar).into_affine());
        assert_eq!(g1_bytes(&g1).as_slice(), bytes(&row["g1"]));
        assert_eq!(g2_bytes(&g2).as_slice(), bytes(&row["g2"]));
        assert_eq!(scalar_from_bytes(&scalar_bytes(&scalar)).unwrap(), scalar);
    }
}

#[test]
fn python_malformed_and_subgroup_vectors_rejected() {
    let v = vectors();
    for row in v["invalid_points"].as_array().unwrap() {
        let raw = bytes(&row["bytes"]);
        let rejected = if row["group"] == 1 {
            g1_from_bytes(&raw).is_err()
        } else {
            g2_from_bytes(&raw).is_err()
        };
        assert!(rejected, "{}", row["name"]);
    }
    for row in v["invalid_scalars"].as_array().unwrap() {
        assert!(scalar_from_bytes(&bytes(row)).is_err());
    }
    for length in [0, 31, 33] {
        assert!(scalar_from_bytes(&vec![0; length]).is_err());
    }
}

#[test]
fn python_context_and_transcript_packets_match() {
    let v = vectors();
    let ContextValue::Map(context) = context_value(&v["context"]) else {
        panic!()
    };
    let encoded = canonical_context(&context).unwrap();
    assert_eq!(encoded, bytes(&v["context_hex"]));
    let mut t = Transcript::new(&encoded, bytes(&v["salt"]).try_into().unwrap());
    for op in v["operations"].as_array().unwrap() {
        let label = op["label"].as_str().unwrap();
        if op["type"] == "absorb" {
            t.absorb(label, &bytes(&op["payload"])).unwrap();
        } else {
            let domains: Vec<_> = op["domains"]
                .as_array()
                .unwrap()
                .iter()
                .map(domain)
                .collect();
            let values = t.challenge_mixed(label, &domains).unwrap();
            let expected: Vec<_> = op["values"]
                .as_array()
                .unwrap()
                .iter()
                .map(|x| Fr::from_str(x.as_str().unwrap()).unwrap())
                .collect();
            assert_eq!(values, expected, "packet {label}");
        }
    }
    assert_eq!(t.query_count(), v["query_count"].as_u64().unwrap());
    assert_eq!(t.event_count(), v["event_count"].as_u64().unwrap());
}

#[test]
fn transcript_rejections_leave_state_unchanged_and_domains_are_bound() {
    let mut t = Transcript::new(b"context", [7; 32]);
    let mut original = t.clone();
    assert!(t.absorb("", b"ignored").is_err());
    assert!(t.challenge("x", 0, Domain::Field).is_err());
    assert!(t.challenge_mixed("x", &[]).is_err());
    assert!(t.challenge("", 3, Domain::Field).is_err());
    assert_eq!(t.event_count(), 0);
    assert_eq!(t.query_count(), 0);
    assert_eq!(
        t.challenge("ok", 3, Domain::Field).unwrap(),
        original.challenge("ok", 3, Domain::Field).unwrap()
    );
    let mut a = Transcript::new(b"context", [7; 32]);
    let mut b = a.clone();
    assert_ne!(
        a.challenge("x", 8, Domain::Field).unwrap(),
        b.challenge("x", 8, Domain::Nonzero).unwrap()
    );
    let mut c = Transcript::new(b"context", [7; 32]);
    assert!(c
        .challenge("x", 64, Domain::Nonboolean)
        .unwrap()
        .iter()
        .all(|x| !x.is_zero() && *x != Fr::one()));
}

#[test]
fn reader_checked_points_lengths_and_trailing_bytes() {
    let mut encoded = scalar_bytes(&Fr::from(7u64)).to_vec();
    encoded.extend_from_slice(&g1_bytes(&G1Affine::identity()));
    encoded.extend_from_slice(&g2_bytes(&G2Affine::generator()));
    encoded.extend_from_slice(&pack_bytes(b"abc"));
    let mut reader = Reader::new(&encoded);
    assert_eq!(reader.scalar().unwrap(), Fr::from(7u64));
    assert!(reader.g1().unwrap().is_zero());
    assert_eq!(reader.g2().unwrap(), G2Affine::generator());
    assert!(reader.finish().is_err());
    assert_eq!(reader.framed_bytes().unwrap(), b"abc");
    reader.finish().unwrap();
    assert_eq!(reader.position(), encoded.len());
    for n in [0, 7] {
        assert!(Reader::new(&vec![0; n]).framed_bytes().is_err());
    }
    assert!(Reader::new(&u64::MAX.to_be_bytes()).framed_bytes().is_err());
    assert!(Reader::new(&encoded[..31]).scalar().is_err());
    assert!(Reader::new(&[0; 47]).g1().is_err());
    assert!(Reader::new(&[0; 95]).g2().is_err());
}

#[test]
fn contexts_require_semantic_fields_and_separate_types() {
    assert!(canonical_context(&BTreeMap::new()).is_err());
    let v = vectors();
    let ContextValue::Map(mut context) = context_value(&v["context"]) else {
        panic!()
    };
    let mut encodings = Vec::new();
    for extra in [
        ContextValue::Null,
        ContextValue::Bool(false),
        0u64.into(),
        ContextValue::Text("0".into()),
        ContextValue::Bytes(b"0".to_vec()),
        ContextValue::List(vec![]),
    ] {
        context.insert("extra".into(), extra);
        let encoded = canonical_context(&context).unwrap();
        assert!(!encodings.contains(&encoded));
        encodings.push(encoded);
    }
    context.remove("E");
    assert!(canonical_context(&context).is_err());
}

#[test]
fn frozen_complete_proof_changes_cross_bucket_weights() {
    let mut a = Transcript::new(b"context", [0; 32]);
    let mut b = a.clone();
    a.absorb("verifier.crossbucket.complete_proof", b"proof-A")
        .unwrap();
    b.absorb("verifier.crossbucket.complete_proof", b"proof-B")
        .unwrap();
    assert_ne!(
        a.challenge("verifier.crossbucket.weights", 4, Domain::Field)
            .unwrap(),
        b.challenge("verifier.crossbucket.weights", 4, Domain::Field)
            .unwrap()
    );
}
