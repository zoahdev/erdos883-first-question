import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_80 :
    (List.ofFn coreChunks618_80).flatten =
      (coreData618.take (coreResources618 80).q).drop 159 := by
  decide +kernel

theorem coreCheck618_80 :
    ∀ c : Fin 1, (coreChunks618_80 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 80)) = true := by
  decide +kernel
#print axioms coreFlatten618_80
#print axioms coreCheck618_80
end Erdos883Verified
