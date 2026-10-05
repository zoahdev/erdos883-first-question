import Erdos883AdaptiveSpan64924Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength64924_1 : adaptiveNumericSpans64924_1.length = 567 := by decide +kernel
theorem adaptiveSpanEvenCache64924_1 : adaptiveSpanEven64924_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain64924_1 : adaptiveSpanEven64924_1.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanEvenEntries64924_1 : adaptiveSpanEven64924_1.spans = coreEvenSpans 32462 0 adaptiveNumericSpans64924_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache64924_1 : adaptiveSpanWhole64924_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain64924_1 : adaptiveSpanWhole64924_1.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanWholeEntries64924_1 : adaptiveSpanWhole64924_1.spans = coreWholeSpans 0 adaptiveNumericSpans64924_1 := by
  decide +kernel
end Erdos883Verified
