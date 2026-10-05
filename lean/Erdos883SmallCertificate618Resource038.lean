import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_38 :
    (List.ofFn coreChunks618_38).flatten =
      (coreData618.take (coreResources618 38).q).drop 80 := by
  decide +kernel

theorem coreCheck618_38 :
    ∀ c : Fin 1, (coreChunks618_38 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 38)) = true := by
  decide +kernel
#print axioms coreFlatten618_38
#print axioms coreCheck618_38
end Erdos883Verified
