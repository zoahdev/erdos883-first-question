import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_11 :
    (List.ofFn coreChunks618_11).flatten =
      (coreData618.take (coreResources618 11).q).drop 118 := by
  decide +kernel

theorem coreCheck618_11 :
    ∀ c : Fin 1, (coreChunks618_11 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 11)) = true := by
  decide +kernel
#print axioms coreFlatten618_11
#print axioms coreCheck618_11
end Erdos883Verified
