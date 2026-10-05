import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_83 :
    (List.ofFn coreChunks618_83).flatten =
      (coreData618.take (coreResources618 83).q).drop 165 := by
  decide +kernel

theorem coreCheck618_83 :
    ∀ c : Fin 1, (coreChunks618_83 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 83)) = true := by
  decide +kernel
#print axioms coreFlatten618_83
#print axioms coreCheck618_83
end Erdos883Verified
