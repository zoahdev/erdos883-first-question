import Erdos883AdaptiveSpan104564Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength104564_0 : adaptiveNumericSpans104564_0.length = 642 := by decide +kernel
theorem adaptiveSpanEvenCache104564_0 : adaptiveSpanEven104564_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain104564_0 : adaptiveSpanEven104564_0.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanEvenEntries104564_0 : adaptiveSpanEven104564_0.spans = coreEvenSpans 52282 0 adaptiveNumericSpans104564_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache104564_0 : adaptiveSpanWhole104564_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain104564_0 : adaptiveSpanWhole104564_0.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanWholeEntries104564_0 : adaptiveSpanWhole104564_0.spans = coreWholeSpans 0 adaptiveNumericSpans104564_0 := by
  decide +kernel
end Erdos883Verified
