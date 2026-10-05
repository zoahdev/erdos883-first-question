import Erdos883AdaptiveSpan104564Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength104564_3 : adaptiveNumericSpans104564_3.length = 642 := by decide +kernel
theorem adaptiveSpanEvenCache104564_3 : adaptiveSpanEven104564_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain104564_3 : adaptiveSpanEven104564_3.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanEvenEntries104564_3 : adaptiveSpanEven104564_3.spans = coreEvenSpans 52282 0 adaptiveNumericSpans104564_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache104564_3 : adaptiveSpanWhole104564_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain104564_3 : adaptiveSpanWhole104564_3.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanWholeEntries104564_3 : adaptiveSpanWhole104564_3.spans = coreWholeSpans 0 adaptiveNumericSpans104564_3 := by
  decide +kernel
end Erdos883Verified
