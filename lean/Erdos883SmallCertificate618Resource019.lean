import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_19 :
    (List.ofFn coreChunks618_19).flatten =
      (coreData618.take (coreResources618 19).q).drop 128 := by
  decide +kernel

theorem coreCheck618_19 :
    ∀ c : Fin 1, (coreChunks618_19 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 19)) = true := by
  decide +kernel
#print axioms coreFlatten618_19
#print axioms coreCheck618_19
end Erdos883Verified
