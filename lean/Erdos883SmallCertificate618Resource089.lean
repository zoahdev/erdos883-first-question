import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_89 :
    (List.ofFn coreChunks618_89).flatten =
      (coreData618.take (coreResources618 89).q).drop 187 := by
  decide +kernel

theorem coreCheck618_89 :
    ∀ c : Fin 1, (coreChunks618_89 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 89)) = true := by
  decide +kernel
#print axioms coreFlatten618_89
#print axioms coreCheck618_89
end Erdos883Verified
